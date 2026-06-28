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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_6, lean_apply_7, lean_apply_9, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,142734480563613395 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,15847151208953044930 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7648019047378041818 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,5867936518352330385 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,5409699204079762053 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,14659826576719934041 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,4071431237389361899 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [67, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,17634999261200945788 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,6038015573457448861 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7664676426519081512 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,11290445982748949970 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,16617897391613630551 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7843916627258953971 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,16668816239785169145 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,1276541560985212704 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,4709293993499401857 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,17764915872583942180 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,14564946645751684478 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,2613367005446990307 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,14660631227684585679 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,5465150556496429213 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,3067006782463195778 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,((( 723085142 as usize) << 1) | 1) as *mut LeanObject,12553131995450129664 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,18336192281881472727 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,6252459286569296447 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,5237802591145334394 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value: LeanStringObject<10> =
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
        m_data: [98, 105, 101, 110, 116, 97, 105, 108, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value: LeanStringObject<5> =
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
        m_data: [114, 101, 102, 108, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value)
                as *mut LeanObject,
            8550510443043304393 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value)
                as *mut LeanObject,
            14477891125163417350 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value)
                as *mut LeanObject,
            3381711156881085428 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value: LeanStringObject<7> =
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
        m_data: [116, 111, 95, 97, 110, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_4: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value)
                as *mut LeanObject,
            3381711156881085428 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_4)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value)
                as *mut LeanObject,
            60168100728142487 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value: LeanStringObject<9> =
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
        m_data: [97, 100, 100, 95, 103, 111, 97, 108, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7951832776404106944 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_4
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value)
                as *mut LeanObject,
            6910639143271370906 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [73, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 72, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 106, 117, 110, 99, 116, 105, 111, 110, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0_value)
            as *mut LeanObject,
        5985446289347889015 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2_value:
    LeanStringObject<31> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7951832776404106944 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_4
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0_value
        ) as *mut LeanObject,
        9067151829802160435 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 117, 114, 101, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 104, 109, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [73, 115, 80, 117, 114, 101, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value) as *mut LeanObject,13332341187416043682 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value) as *mut LeanObject,18273640022974733293 as *mut LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7951832776404106944 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_4
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value
        ) as *mut LeanObject,
        3096500988654044041 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7951832776404106944 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_4
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value)
            as *mut LeanObject,
        10222155196932631968 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7951832776404106944 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_4
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value
        ) as *mut LeanObject,
        15714647072058212852 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7951832776404106944 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_4
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value)
            as *mut LeanObject,
        4725788427437577091 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4_value: LeanStringObject<
    53,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6_value: LeanStringObject<
    67,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8_value)
            as *mut LeanObject,
        4341430929543422322 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12_value:
    LeanStringObject<14> = LeanStringObject {
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
        97, 110, 100, 95, 111, 114, 95, 101, 108, 105, 109, 95, 114, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12_value)
            as *mut LeanObject,
        1847820319560413069 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2_value) as *mut LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0_value) as *mut LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value) as *mut LeanObject,7870113334857981723 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1_value) as *mut LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0_value: LeanStringObject<158> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value: LeanStringObject<7> =
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
        m_data: [109, 99, 97, 115, 101, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value)
                as *mut LeanObject,
            1713051840268779758 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 77, 67, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value) as *mut LeanObject,7471086871523061247 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    v___x_3432_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_;
    v___x_3433_ = 0;
    v___x_3434_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_;
    v___x_3435_ = l_Lean_registerTraceClass(v___x_3432_, v___x_3433_, v___x_3434_);
    return v___x_3435_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2____boxed(
    mut v_a_3436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3437_: *mut LeanObject = core::ptr::null_mut();
    v_res_3437_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
    return v_res_3437_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(
    mut v_u_3467_: *mut LeanObject,
    mut v_00_u03c3s_3468_: *mut LeanObject,
    mut v_H_3469_: *mut LeanObject,
    mut v_a_3470_: *mut LeanObject,
    mut v_a_3471_: *mut LeanObject,
    mut v_a_3472_: *mut LeanObject,
    mut v_a_3473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3477_: u8 = 0;
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: u8 = 0;
    let mut v___x_3484_: u8 = 0;
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3490_: u8 = 0;
    let mut v_snd_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3494_: u8 = 0;
    let mut v_snd_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v_fst_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3503_: u8 = 0;
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3521_: u8 = 0;
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut v_unused_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3524_: u8 = 0;
    let mut v_unused_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3526_: u8 = 0;
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: u8 = 0;
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3550_: u8 = 0;
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3562_: u8 = 0;
    let mut v_a_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3564_: u8 = 0;
    let mut v_a_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3485_ = l_Lean_Expr_consumeMData(v_H_3469_);
                v___x_3486_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v___x_3485_);
                lean_dec_ref(v___x_3485_);
                if lean_obj_tag(v___x_3486_) == 1 {
                    v_val_3487_ = lean_ctor_get(v___x_3486_, 0);
                    v_isSharedCheck_3526_ = (!lean_is_exclusive(v___x_3486_)) as u8;
                    if v_isSharedCheck_3526_ == 0 {
                        v___x_3489_ = v___x_3486_;
                        v_isShared_3490_ = v_isSharedCheck_3526_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_3487_);
                        lean_dec(v___x_3486_);
                        v___x_3489_ = lean_box(0);
                        v_isShared_3490_ = v_isSharedCheck_3526_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3486_);
                    v___x_3527_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5;
                    v___x_3528_ = lean_box(0);
                    v___x_3529_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3529_, 0, v_u_3467_);
                    lean_ctor_set(v___x_3529_, 1, v___x_3528_);
                    lean_inc_ref(v___x_3529_);
                    v___x_3530_ = l_Lean_mkConst(v___x_3527_, v___x_3529_);
                    lean_inc_ref(v_00_u03c3s_3468_);
                    v___x_3531_ = l_Lean_Expr_app___override(v___x_3530_, v_00_u03c3s_3468_);
                    v___x_3532_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3532_, 0, v___x_3531_);
                    v___x_3533_ = 0;
                    v___x_3534_ = lean_box(0);
                    lean_inc_ref(v___x_3532_);
                    v___x_3535_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_3532_,
                        v___x_3533_,
                        v___x_3534_,
                        v_a_3470_,
                        v_a_3471_,
                        v_a_3472_,
                        v_a_3473_,
                    );
                    if lean_obj_tag(v___x_3535_) == 0 {
                        v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
                        lean_inc(v_a_3536_);
                        lean_dec_ref_known(v___x_3535_, 1);
                        v___x_3537_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_3532_,
                            v___x_3533_,
                            v___x_3534_,
                            v_a_3470_,
                            v_a_3471_,
                            v_a_3472_,
                            v_a_3473_,
                        );
                        if lean_obj_tag(v___x_3537_) == 0 {
                            v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
                            v_isSharedCheck_3564_ = (!lean_is_exclusive(v___x_3537_)) as u8;
                            if v_isSharedCheck_3564_ == 0 {
                                v___x_3540_ = v___x_3537_;
                                v_isShared_3541_ = v_isSharedCheck_3564_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_3538_);
                                lean_dec(v___x_3537_);
                                v___x_3540_ = lean_box(0);
                                v_isShared_3541_ = v_isSharedCheck_3564_;
                                state = 11;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3536_);
                            lean_dec_ref_known(v___x_3529_, 2);
                            lean_dec_ref(v_H_3469_);
                            lean_dec_ref(v_00_u03c3s_3468_);
                            v_a_3565_ = lean_ctor_get(v___x_3537_, 0);
                            lean_inc(v_a_3565_);
                            lean_dec_ref_known(v___x_3537_, 1);
                            v_a_3482_ = v_a_3565_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_3532_, 1);
                        lean_dec_ref_known(v___x_3529_, 2);
                        lean_dec_ref(v_H_3469_);
                        lean_dec_ref(v_00_u03c3s_3468_);
                        v_a_3566_ = lean_ctor_get(v___x_3535_, 0);
                        lean_inc(v_a_3566_);
                        lean_dec_ref_known(v___x_3535_, 1);
                        v_a_3482_ = v_a_3566_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3477_ == 0 {
                    lean_dec_ref(v___y_3476_);
                    v___x_3478_ = lean_box(0);
                    v___x_3479_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3479_, 0, v___x_3478_);
                    return v___x_3479_;
                } else {
                    v___x_3480_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3480_, 0, v___y_3476_);
                    return v___x_3480_;
                }
            }
            2 => {
                v___x_3483_ = l_Lean_Exception_isInterrupt(v_a_3482_);
                if v___x_3483_ == 0 {
                    lean_inc_ref(v_a_3482_);
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
                v_snd_3491_ = lean_ctor_get(v_val_3487_, 1);
                v_isSharedCheck_3524_ = (!lean_is_exclusive(v_val_3487_)) as u8;
                if v_isSharedCheck_3524_ == 0 {
                    v_unused_3525_ = lean_ctor_get(v_val_3487_, 0);
                    lean_dec(v_unused_3525_);
                    v___x_3493_ = v_val_3487_;
                    v_isShared_3494_ = v_isSharedCheck_3524_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_3491_);
                    lean_dec(v_val_3487_);
                    v___x_3493_ = lean_box(0);
                    v_isShared_3494_ = v_isSharedCheck_3524_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_snd_3495_ = lean_ctor_get(v_snd_3491_, 1);
                v_isSharedCheck_3522_ = (!lean_is_exclusive(v_snd_3491_)) as u8;
                if v_isSharedCheck_3522_ == 0 {
                    v_unused_3523_ = lean_ctor_get(v_snd_3491_, 0);
                    lean_dec(v_unused_3523_);
                    v___x_3497_ = v_snd_3491_;
                    v_isShared_3498_ = v_isSharedCheck_3522_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_3495_);
                    lean_dec(v_snd_3491_);
                    v___x_3497_ = lean_box(0);
                    v_isShared_3498_ = v_isSharedCheck_3522_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_fst_3499_ = lean_ctor_get(v_snd_3495_, 0);
                v_snd_3500_ = lean_ctor_get(v_snd_3495_, 1);
                v_isSharedCheck_3521_ = (!lean_is_exclusive(v_snd_3495_)) as u8;
                if v_isSharedCheck_3521_ == 0 {
                    v___x_3502_ = v_snd_3495_;
                    v_isShared_3503_ = v_isSharedCheck_3521_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_snd_3500_);
                    lean_inc(v_fst_3499_);
                    lean_dec(v_snd_3495_);
                    v___x_3502_ = lean_box(0);
                    v_isShared_3503_ = v_isSharedCheck_3521_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3504_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4;
                v___x_3505_ = lean_box(0);
                if v_isShared_3494_ == 0 {
                    lean_ctor_set_tag(v___x_3493_, 1);
                    lean_ctor_set(v___x_3493_, 1, v___x_3505_);
                    lean_ctor_set(v___x_3493_, 0, v_u_3467_);
                    v___x_3507_ = v___x_3493_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_u_3467_);
                    lean_ctor_set(v_reuseFailAlloc_3520_, 1, v___x_3505_);
                    v___x_3507_ = v_reuseFailAlloc_3520_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3508_ = l_Lean_mkConst(v___x_3504_, v___x_3507_);
                v___x_3509_ = l_Lean_mkAppB(v___x_3508_, v_00_u03c3s_3468_, v_H_3469_);
                if v_isShared_3503_ == 0 {
                    lean_ctor_set(v___x_3502_, 1, v___x_3509_);
                    lean_ctor_set(v___x_3502_, 0, v_snd_3500_);
                    v___x_3511_ = v___x_3502_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_snd_3500_);
                    lean_ctor_set(v_reuseFailAlloc_3519_, 1, v___x_3509_);
                    v___x_3511_ = v_reuseFailAlloc_3519_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3498_ == 0 {
                    lean_ctor_set(v___x_3497_, 1, v___x_3511_);
                    lean_ctor_set(v___x_3497_, 0, v_fst_3499_);
                    v___x_3513_ = v___x_3497_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_fst_3499_);
                    lean_ctor_set(v_reuseFailAlloc_3518_, 1, v___x_3511_);
                    v___x_3513_ = v_reuseFailAlloc_3518_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3490_ == 0 {
                    lean_ctor_set(v___x_3489_, 0, v___x_3513_);
                    v___x_3515_ = v___x_3489_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3513_);
                    v___x_3515_ = v_reuseFailAlloc_3517_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3516_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3516_, 0, v___x_3515_);
                return v___x_3516_;
            }
            11 => {
                v___x_3542_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7;
                lean_inc_ref(v___x_3529_);
                v___x_3543_ = l_Lean_mkConst(v___x_3542_, v___x_3529_);
                lean_inc(v_a_3538_);
                lean_inc(v_a_3536_);
                lean_inc_ref(v_H_3469_);
                lean_inc_ref(v_00_u03c3s_3468_);
                v___x_3544_ = l_Lean_mkApp4(
                    v___x_3543_,
                    v_00_u03c3s_3468_,
                    v_H_3469_,
                    v_a_3536_,
                    v_a_3538_,
                );
                v___x_3545_ = lean_box(0);
                v___x_3546_ = l_Lean_Meta_synthInstance(
                    v___x_3544_,
                    v___x_3545_,
                    v_a_3470_,
                    v_a_3471_,
                    v_a_3472_,
                    v_a_3473_,
                );
                if lean_obj_tag(v___x_3546_) == 0 {
                    v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
                    v_isSharedCheck_3562_ = (!lean_is_exclusive(v___x_3546_)) as u8;
                    if v_isSharedCheck_3562_ == 0 {
                        v___x_3549_ = v___x_3546_;
                        v_isShared_3550_ = v_isSharedCheck_3562_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_3547_);
                        lean_dec(v___x_3546_);
                        v___x_3549_ = lean_box(0);
                        v_isShared_3550_ = v_isSharedCheck_3562_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3540_);
                    lean_dec(v_a_3538_);
                    lean_dec(v_a_3536_);
                    lean_dec_ref_known(v___x_3529_, 2);
                    lean_dec_ref(v_H_3469_);
                    lean_dec_ref(v_00_u03c3s_3468_);
                    v_a_3563_ = lean_ctor_get(v___x_3546_, 0);
                    lean_inc(v_a_3563_);
                    lean_dec_ref_known(v___x_3546_, 1);
                    v_a_3482_ = v_a_3563_;
                    state = 2;
                    continue;
                }
            }
            12 => {
                v___x_3551_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9;
                v___x_3552_ = l_Lean_mkConst(v___x_3551_, v___x_3529_);
                lean_inc(v_a_3538_);
                lean_inc(v_a_3536_);
                v___x_3553_ = l_Lean_mkApp5(
                    v___x_3552_,
                    v_00_u03c3s_3468_,
                    v_H_3469_,
                    v_a_3536_,
                    v_a_3538_,
                    v_a_3547_,
                );
                v___x_3554_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3554_, 0, v_a_3538_);
                lean_ctor_set(v___x_3554_, 1, v___x_3553_);
                v___x_3555_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3555_, 0, v_a_3536_);
                lean_ctor_set(v___x_3555_, 1, v___x_3554_);
                if v_isShared_3541_ == 0 {
                    lean_ctor_set_tag(v___x_3540_, 1);
                    lean_ctor_set(v___x_3540_, 0, v___x_3555_);
                    v___x_3557_ = v___x_3540_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3555_);
                    v___x_3557_ = v_reuseFailAlloc_3561_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3550_ == 0 {
                    lean_ctor_set(v___x_3549_, 0, v___x_3557_);
                    v___x_3559_ = v___x_3549_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
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
    mut v_u_3567_: *mut LeanObject,
    mut v_00_u03c3s_3568_: *mut LeanObject,
    mut v_H_3569_: *mut LeanObject,
    mut v_a_3570_: *mut LeanObject,
    mut v_a_3571_: *mut LeanObject,
    mut v_a_3572_: *mut LeanObject,
    mut v_a_3573_: *mut LeanObject,
    mut v_a_3574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3575_: *mut LeanObject = core::ptr::null_mut();
    v_res_3575_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(
        v_u_3567_,
        v_00_u03c3s_3568_,
        v_H_3569_,
        v_a_3570_,
        v_a_3571_,
        v_a_3572_,
        v_a_3573_,
    );
    lean_dec(v_a_3573_);
    lean_dec_ref(v_a_3572_);
    lean_dec(v_a_3571_);
    lean_dec_ref(v_a_3570_);
    return v_res_3575_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(
    mut v_u_3584_: *mut LeanObject,
    mut v_goals_3585_: *mut LeanObject,
    mut v_00_u03c3s_3586_: *mut LeanObject,
    mut v_T_3587_: *mut LeanObject,
    mut v_Q_3588_: *mut LeanObject,
    mut v_H_3589_: *mut LeanObject,
    mut v_a_3590_: *mut LeanObject,
    mut v_a_3591_: *mut LeanObject,
    mut v_a_3592_: *mut LeanObject,
    mut v_a_3593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3600_: u8 = 0;
    let mut v_goal_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3608_: u8 = 0;
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v_a_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3632_: u8 = 0;
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3636_: u8 = 0;
    let mut v_isSharedCheck_3637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_H_3589_);
                lean_inc_ref(v_Q_3588_);
                lean_inc_ref(v_00_u03c3s_3586_);
                lean_inc(v_u_3584_);
                v___x_3595_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                    v_u_3584_,
                    v_00_u03c3s_3586_,
                    v_Q_3588_,
                    v_H_3589_,
                );
                v_fst_3596_ = lean_ctor_get(v___x_3595_, 0);
                v_snd_3597_ = lean_ctor_get(v___x_3595_, 1);
                v_isSharedCheck_3637_ = (!lean_is_exclusive(v___x_3595_)) as u8;
                if v_isSharedCheck_3637_ == 0 {
                    v___x_3599_ = v___x_3595_;
                    v_isShared_3600_ = v_isSharedCheck_3637_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3597_);
                    lean_inc(v_fst_3596_);
                    lean_dec(v___x_3595_);
                    v___x_3599_ = lean_box(0);
                    v_isShared_3600_ = v_isSharedCheck_3637_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_T_3587_);
                lean_inc(v_fst_3596_);
                lean_inc_ref(v_00_u03c3s_3586_);
                lean_inc(v_u_3584_);
                v_goal_3601_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v_goal_3601_, 0, v_u_3584_);
                lean_ctor_set(v_goal_3601_, 1, v_00_u03c3s_3586_);
                lean_ctor_set(v_goal_3601_, 2, v_fst_3596_);
                lean_ctor_set(v_goal_3601_, 3, v_T_3587_);
                v___x_3602_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_3601_);
                v___x_3603_ = lean_box(0);
                v___x_3604_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_3602_,
                    v___x_3603_,
                    v_a_3590_,
                    v_a_3591_,
                    v_a_3592_,
                    v_a_3593_,
                );
                if lean_obj_tag(v___x_3604_) == 0 {
                    v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
                    v_isSharedCheck_3628_ = (!lean_is_exclusive(v___x_3604_)) as u8;
                    if v_isSharedCheck_3628_ == 0 {
                        v___x_3607_ = v___x_3604_;
                        v_isShared_3608_ = v_isSharedCheck_3628_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3605_);
                        lean_dec(v___x_3604_);
                        v___x_3607_ = lean_box(0);
                        v_isShared_3608_ = v_isSharedCheck_3628_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3599_);
                    lean_dec(v_snd_3597_);
                    lean_dec(v_fst_3596_);
                    lean_dec_ref(v_H_3589_);
                    lean_dec_ref(v_Q_3588_);
                    lean_dec_ref(v_T_3587_);
                    lean_dec_ref(v_00_u03c3s_3586_);
                    lean_dec(v_u_3584_);
                    v_a_3629_ = lean_ctor_get(v___x_3604_, 0);
                    v_isSharedCheck_3636_ = (!lean_is_exclusive(v___x_3604_)) as u8;
                    if v_isSharedCheck_3636_ == 0 {
                        v___x_3631_ = v___x_3604_;
                        v_isShared_3632_ = v_isSharedCheck_3636_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3629_);
                        lean_dec(v___x_3604_);
                        v___x_3631_ = lean_box(0);
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
                v___x_3614_ = lean_box(0);
                lean_inc_n(v_u_3584_, 2);
                v___x_3615_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3615_, 0, v_u_3584_);
                lean_ctor_set(v___x_3615_, 1, v___x_3614_);
                v___x_3616_ = l_Lean_mkConst(v___x_3613_, v___x_3615_);
                lean_inc_ref(v_T_3587_);
                lean_inc_ref(v_H_3589_);
                lean_inc_ref(v_Q_3588_);
                lean_inc_ref_n(v_00_u03c3s_3586_, 2);
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
                v___x_3619_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_3619_, 0, v_u_3584_);
                lean_ctor_set(v___x_3619_, 1, v_00_u03c3s_3586_);
                lean_ctor_set(v___x_3619_, 2, v___x_3618_);
                lean_ctor_set(v___x_3619_, 3, v_T_3587_);
                v___x_3620_ = lean_box(0);
                if v_isShared_3600_ == 0 {
                    lean_ctor_set(v___x_3599_, 1, v___x_3617_);
                    lean_ctor_set(v___x_3599_, 0, v___x_3619_);
                    v___x_3622_ = v___x_3599_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3619_);
                    lean_ctor_set(v_reuseFailAlloc_3627_, 1, v___x_3617_);
                    v___x_3622_ = v_reuseFailAlloc_3627_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3623_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3623_, 0, v___x_3620_);
                lean_ctor_set(v___x_3623_, 1, v___x_3622_);
                if v_isShared_3608_ == 0 {
                    lean_ctor_set(v___x_3607_, 0, v___x_3623_);
                    v___x_3625_ = v___x_3607_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3623_);
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
                    v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
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
    mut v_u_3638_: *mut LeanObject,
    mut v_goals_3639_: *mut LeanObject,
    mut v_00_u03c3s_3640_: *mut LeanObject,
    mut v_T_3641_: *mut LeanObject,
    mut v_Q_3642_: *mut LeanObject,
    mut v_H_3643_: *mut LeanObject,
    mut v_a_3644_: *mut LeanObject,
    mut v_a_3645_: *mut LeanObject,
    mut v_a_3646_: *mut LeanObject,
    mut v_a_3647_: *mut LeanObject,
    mut v_a_3648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3649_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3647_);
    lean_dec_ref(v_a_3646_);
    lean_dec(v_a_3645_);
    lean_dec_ref(v_a_3644_);
    lean_dec(v_goals_3639_);
    return v_res_3649_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(
    mut v_msgData_3650_: *mut LeanObject,
    mut v___y_3651_: *mut LeanObject,
    mut v___y_3652_: *mut LeanObject,
    mut v___y_3653_: *mut LeanObject,
    mut v___y_3654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    v___x_3656_ = lean_st_ref_get(v___y_3654_);
    v_env_3657_ = lean_ctor_get(v___x_3656_, 0);
    lean_inc_ref(v_env_3657_);
    lean_dec(v___x_3656_);
    v___x_3658_ = lean_st_ref_get(v___y_3652_);
    v_mctx_3659_ = lean_ctor_get(v___x_3658_, 0);
    lean_inc_ref(v_mctx_3659_);
    lean_dec(v___x_3658_);
    v_lctx_3660_ = lean_ctor_get(v___y_3651_, 2);
    v_options_3661_ = lean_ctor_get(v___y_3653_, 2);
    lean_inc_ref(v_options_3661_);
    lean_inc_ref(v_lctx_3660_);
    v___x_3662_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3662_, 0, v_env_3657_);
    lean_ctor_set(v___x_3662_, 1, v_mctx_3659_);
    lean_ctor_set(v___x_3662_, 2, v_lctx_3660_);
    lean_ctor_set(v___x_3662_, 3, v_options_3661_);
    v___x_3663_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3663_, 0, v___x_3662_);
    lean_ctor_set(v___x_3663_, 1, v_msgData_3650_);
    v___x_3664_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3664_, 0, v___x_3663_);
    return v___x_3664_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0___boxed(
    mut v_msgData_3665_: *mut LeanObject,
    mut v___y_3666_: *mut LeanObject,
    mut v___y_3667_: *mut LeanObject,
    mut v___y_3668_: *mut LeanObject,
    mut v___y_3669_: *mut LeanObject,
    mut v___y_3670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3671_: *mut LeanObject = core::ptr::null_mut();
    v_res_3671_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msgData_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
    lean_dec(v___y_3669_);
    lean_dec_ref(v___y_3668_);
    lean_dec(v___y_3667_);
    lean_dec_ref(v___y_3666_);
    return v_res_3671_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(
    mut v_msg_3672_: *mut LeanObject,
    mut v___y_3673_: *mut LeanObject,
    mut v___y_3674_: *mut LeanObject,
    mut v___y_3675_: *mut LeanObject,
    mut v___y_3676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3683_: u8 = 0;
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3678_ = lean_ctor_get(v___y_3675_, 5);
                v___x_3679_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
                v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
                v_isSharedCheck_3688_ = (!lean_is_exclusive(v___x_3679_)) as u8;
                if v_isSharedCheck_3688_ == 0 {
                    v___x_3682_ = v___x_3679_;
                    v_isShared_3683_ = v_isSharedCheck_3688_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3680_);
                    lean_dec(v___x_3679_);
                    v___x_3682_ = lean_box(0);
                    v_isShared_3683_ = v_isSharedCheck_3688_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3678_);
                v___x_3684_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3684_, 0, v_ref_3678_);
                lean_ctor_set(v___x_3684_, 1, v_a_3680_);
                if v_isShared_3683_ == 0 {
                    lean_ctor_set_tag(v___x_3682_, 1);
                    lean_ctor_set(v___x_3682_, 0, v___x_3684_);
                    v___x_3686_ = v___x_3682_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3684_);
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
    mut v_msg_3689_: *mut LeanObject,
    mut v___y_3690_: *mut LeanObject,
    mut v___y_3691_: *mut LeanObject,
    mut v___y_3692_: *mut LeanObject,
    mut v___y_3693_: *mut LeanObject,
    mut v___y_3694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3695_: *mut LeanObject = core::ptr::null_mut();
    v_res_3695_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
    lean_dec(v___y_3693_);
    lean_dec_ref(v___y_3692_);
    lean_dec(v___y_3691_);
    lean_dec_ref(v___y_3690_);
    return v_res_3695_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1()
-> *mut LeanObject {
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    v___x_3697_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0;
    v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
    return v___x_3698_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(
    mut v_goal_3699_: *mut LeanObject,
    mut v_a_3700_: *mut LeanObject,
    mut v_a_3701_: *mut LeanObject,
    mut v_a_3702_: *mut LeanObject,
    mut v_a_3703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hyps_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3710_: u8 = 0;
    let mut v_snd_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hyps_3705_ = lean_ctor_get(v_goal_3699_, 2);
                lean_inc_ref(v_hyps_3705_);
                lean_dec_ref(v_goal_3699_);
                v___x_3706_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_hyps_3705_);
                if lean_obj_tag(v___x_3706_) == 1 {
                    lean_dec_ref(v_hyps_3705_);
                    v_val_3707_ = lean_ctor_get(v___x_3706_, 0);
                    v_isSharedCheck_3716_ = (!lean_is_exclusive(v___x_3706_)) as u8;
                    if v_isSharedCheck_3716_ == 0 {
                        v___x_3709_ = v___x_3706_;
                        v_isShared_3710_ = v_isSharedCheck_3716_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3707_);
                        lean_dec(v___x_3706_);
                        v___x_3709_ = lean_box(0);
                        v_isShared_3710_ = v_isSharedCheck_3716_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3706_);
                    v___x_3717_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1);
                    v___x_3718_ = l_Lean_MessageData_ofExpr(v_hyps_3705_);
                    v___x_3719_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3719_, 0, v___x_3717_);
                    lean_ctor_set(v___x_3719_, 1, v___x_3718_);
                    v___x_3720_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_3719_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
                    return v___x_3720_;
                }
            }
            1 => {
                v_snd_3711_ = lean_ctor_get(v_val_3707_, 1);
                lean_inc(v_snd_3711_);
                lean_dec(v_val_3707_);
                v_snd_3712_ = lean_ctor_get(v_snd_3711_, 1);
                lean_inc(v_snd_3712_);
                lean_dec(v_snd_3711_);
                if v_isShared_3710_ == 0 {
                    lean_ctor_set_tag(v___x_3709_, 0);
                    lean_ctor_set(v___x_3709_, 0, v_snd_3712_);
                    v___x_3714_ = v___x_3709_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_snd_3712_);
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
    mut v_goal_3721_: *mut LeanObject,
    mut v_a_3722_: *mut LeanObject,
    mut v_a_3723_: *mut LeanObject,
    mut v_a_3724_: *mut LeanObject,
    mut v_a_3725_: *mut LeanObject,
    mut v_a_3726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3727_: *mut LeanObject = core::ptr::null_mut();
    v_res_3727_ =
        l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(
            v_goal_3721_,
            v_a_3722_,
            v_a_3723_,
            v_a_3724_,
            v_a_3725_,
        );
    lean_dec(v_a_3725_);
    lean_dec_ref(v_a_3724_);
    lean_dec(v_a_3723_);
    lean_dec_ref(v_a_3722_);
    return v_res_3727_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(
    mut v_00_u03b1_3728_: *mut LeanObject,
    mut v_msg_3729_: *mut LeanObject,
    mut v___y_3730_: *mut LeanObject,
    mut v___y_3731_: *mut LeanObject,
    mut v___y_3732_: *mut LeanObject,
    mut v___y_3733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    v___x_3735_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
    return v___x_3735_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___boxed(
    mut v_00_u03b1_3736_: *mut LeanObject,
    mut v_msg_3737_: *mut LeanObject,
    mut v___y_3738_: *mut LeanObject,
    mut v___y_3739_: *mut LeanObject,
    mut v___y_3740_: *mut LeanObject,
    mut v___y_3741_: *mut LeanObject,
    mut v___y_3742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3743_: *mut LeanObject = core::ptr::null_mut();
    v_res_3743_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(v_00_u03b1_3736_, v_msg_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
    lean_dec(v___y_3741_);
    lean_dec_ref(v___y_3740_);
    lean_dec(v___y_3739_);
    lean_dec_ref(v___y_3738_);
    return v_res_3743_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(
    mut v___x_3744_: *mut LeanObject,
    mut v_snd_3745_: *mut LeanObject,
    mut v_k_3746_: *mut LeanObject,
    mut v___x_3747_: u8,
    mut v___x_3748_: *mut LeanObject,
    mut v___x_3749_: *mut LeanObject,
    mut v___x_3750_: *mut LeanObject,
    mut v___x_3751_: *mut LeanObject,
    mut v___x_3752_: *mut LeanObject,
    mut v___x_3753_: *mut LeanObject,
    mut v_H_3754_: *mut LeanObject,
    mut v_x_3755_: *mut LeanObject,
    mut v___y_3756_: *mut LeanObject,
    mut v___y_3757_: *mut LeanObject,
    mut v___y_3758_: *mut LeanObject,
    mut v___y_3759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: u8 = 0;
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3771_: u8 = 0;
    let mut v_fst_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3776_: u8 = 0;
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3793_: u8 = 0;
    let mut v_u_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3799_: u8 = 0;
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3823_: u8 = 0;
    let mut v_unused_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3825_: u8 = 0;
    let mut v_a_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3829_: u8 = 0;
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3833_: u8 = 0;
    let mut v_a_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3837_: u8 = 0;
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3841_: u8 = 0;
    let mut v_isSharedCheck_3842_: u8 = 0;
    let mut v_unused_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut v_isSharedCheck_3853_: u8 = 0;
    let mut v_a_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_3761_ = lean_ctor_get(v___y_3756_, 2);
                lean_inc_ref(v___x_3744_);
                v___x_3762_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3762_, 0, v___x_3744_);
                v___x_3763_ = 0;
                lean_inc_ref(v_x_3755_);
                lean_inc_ref(v_lctx_3761_);
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
                if lean_obj_tag(v___x_3764_) == 0 {
                    lean_dec_ref_known(v___x_3764_, 1);
                    lean_inc(v___y_3759_);
                    lean_inc_ref(v___y_3758_);
                    lean_inc(v___y_3757_);
                    lean_inc_ref(v___y_3756_);
                    lean_inc_ref(v_x_3755_);
                    v___x_3765_ = lean_apply_6(
                        v_k_3746_,
                        v_x_3755_,
                        v___y_3756_,
                        v___y_3757_,
                        v___y_3758_,
                        v___y_3759_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3765_) == 0 {
                        v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
                        lean_inc(v_a_3766_);
                        lean_dec_ref_known(v___x_3765_, 1);
                        v_snd_3767_ = lean_ctor_get(v_a_3766_, 1);
                        v_fst_3768_ = lean_ctor_get(v_a_3766_, 0);
                        v_isSharedCheck_3853_ = (!lean_is_exclusive(v_a_3766_)) as u8;
                        if v_isSharedCheck_3853_ == 0 {
                            v___x_3770_ = v_a_3766_;
                            v_isShared_3771_ = v_isSharedCheck_3853_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_3767_);
                            lean_inc(v_fst_3768_);
                            lean_dec(v_a_3766_);
                            v___x_3770_ = lean_box(0);
                            v_isShared_3771_ = v_isSharedCheck_3853_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_x_3755_);
                        lean_dec_ref(v_H_3754_);
                        lean_dec_ref(v___x_3753_);
                        lean_dec_ref(v___x_3752_);
                        lean_dec_ref(v___x_3751_);
                        lean_dec_ref(v___x_3750_);
                        lean_dec_ref(v___x_3749_);
                        lean_dec_ref(v___x_3748_);
                        lean_dec_ref(v___x_3744_);
                        return v___x_3765_;
                    }
                } else {
                    lean_dec_ref(v_x_3755_);
                    lean_dec_ref(v_H_3754_);
                    lean_dec_ref(v___x_3753_);
                    lean_dec_ref(v___x_3752_);
                    lean_dec_ref(v___x_3751_);
                    lean_dec_ref(v___x_3750_);
                    lean_dec_ref(v___x_3749_);
                    lean_dec_ref(v___x_3748_);
                    lean_dec_ref(v_k_3746_);
                    lean_dec_ref(v___x_3744_);
                    v_a_3854_ = lean_ctor_get(v___x_3764_, 0);
                    v_isSharedCheck_3861_ = (!lean_is_exclusive(v___x_3764_)) as u8;
                    if v_isSharedCheck_3861_ == 0 {
                        v___x_3856_ = v___x_3764_;
                        v_isShared_3857_ = v_isSharedCheck_3861_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3854_);
                        lean_dec(v___x_3764_);
                        v___x_3856_ = lean_box(0);
                        v_isShared_3857_ = v_isSharedCheck_3861_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3772_ = lean_ctor_get(v_snd_3767_, 0);
                v_snd_3773_ = lean_ctor_get(v_snd_3767_, 1);
                v_isSharedCheck_3852_ = (!lean_is_exclusive(v_snd_3767_)) as u8;
                if v_isSharedCheck_3852_ == 0 {
                    v___x_3775_ = v_snd_3767_;
                    v_isShared_3776_ = v_isSharedCheck_3852_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3773_);
                    lean_inc(v_fst_3772_);
                    lean_dec(v_snd_3767_);
                    v___x_3775_ = lean_box(0);
                    v_isShared_3776_ = v_isSharedCheck_3852_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_fst_3772_);
                v___x_3777_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_3772_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
                if lean_obj_tag(v___x_3777_) == 0 {
                    v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
                    lean_inc(v_a_3778_);
                    lean_dec_ref_known(v___x_3777_, 1);
                    v_fst_3779_ = lean_ctor_get(v_a_3778_, 0);
                    v_isSharedCheck_3842_ = (!lean_is_exclusive(v_a_3778_)) as u8;
                    if v_isSharedCheck_3842_ == 0 {
                        v_unused_3843_ = lean_ctor_get(v_a_3778_, 1);
                        lean_dec(v_unused_3843_);
                        v___x_3781_ = v_a_3778_;
                        v_isShared_3782_ = v_isSharedCheck_3842_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_fst_3779_);
                        lean_dec(v_a_3778_);
                        v___x_3781_ = lean_box(0);
                        v_isShared_3782_ = v_isSharedCheck_3842_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3775_);
                    lean_dec(v_snd_3773_);
                    lean_dec(v_fst_3772_);
                    lean_del_object(v___x_3770_);
                    lean_dec(v_fst_3768_);
                    lean_dec_ref(v_x_3755_);
                    lean_dec_ref(v_H_3754_);
                    lean_dec_ref(v___x_3753_);
                    lean_dec_ref(v___x_3752_);
                    lean_dec_ref(v___x_3751_);
                    lean_dec_ref(v___x_3750_);
                    lean_dec_ref(v___x_3749_);
                    lean_dec_ref(v___x_3748_);
                    lean_dec_ref(v___x_3744_);
                    v_a_3844_ = lean_ctor_get(v___x_3777_, 0);
                    v_isSharedCheck_3851_ = (!lean_is_exclusive(v___x_3777_)) as u8;
                    if v_isSharedCheck_3851_ == 0 {
                        v___x_3846_ = v___x_3777_;
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_3844_);
                        lean_dec(v___x_3777_);
                        v___x_3846_ = lean_box(0);
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 15;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc_ref(v___x_3744_);
                v___x_3783_ = l_Lean_Meta_getLevel(
                    v___x_3744_,
                    v___y_3756_,
                    v___y_3757_,
                    v___y_3758_,
                    v___y_3759_,
                );
                if lean_obj_tag(v___x_3783_) == 0 {
                    v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
                    lean_inc(v_a_3784_);
                    lean_dec_ref_known(v___x_3783_, 1);
                    v___x_3785_ = lean_unsigned_to_nat(1);
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
                    lean_dec_ref(v___x_3787_);
                    if lean_obj_tag(v___x_3789_) == 0 {
                        v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
                        v_isSharedCheck_3825_ = (!lean_is_exclusive(v___x_3789_)) as u8;
                        if v_isSharedCheck_3825_ == 0 {
                            v___x_3792_ = v___x_3789_;
                            v_isShared_3793_ = v_isSharedCheck_3825_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3790_);
                            lean_dec(v___x_3789_);
                            v___x_3792_ = lean_box(0);
                            v_isShared_3793_ = v_isSharedCheck_3825_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3784_);
                        lean_del_object(v___x_3781_);
                        lean_dec(v_fst_3779_);
                        lean_del_object(v___x_3775_);
                        lean_dec(v_fst_3772_);
                        lean_del_object(v___x_3770_);
                        lean_dec(v_fst_3768_);
                        lean_dec_ref(v_H_3754_);
                        lean_dec_ref(v___x_3753_);
                        lean_dec_ref(v___x_3752_);
                        lean_dec_ref(v___x_3751_);
                        lean_dec_ref(v___x_3750_);
                        lean_dec_ref(v___x_3749_);
                        lean_dec_ref(v___x_3748_);
                        lean_dec_ref(v___x_3744_);
                        v_a_3826_ = lean_ctor_get(v___x_3789_, 0);
                        v_isSharedCheck_3833_ = (!lean_is_exclusive(v___x_3789_)) as u8;
                        if v_isSharedCheck_3833_ == 0 {
                            v___x_3828_ = v___x_3789_;
                            v_isShared_3829_ = v_isSharedCheck_3833_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_3826_);
                            lean_dec(v___x_3789_);
                            v___x_3828_ = lean_box(0);
                            v_isShared_3829_ = v_isSharedCheck_3833_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3781_);
                    lean_dec(v_fst_3779_);
                    lean_del_object(v___x_3775_);
                    lean_dec(v_snd_3773_);
                    lean_dec(v_fst_3772_);
                    lean_del_object(v___x_3770_);
                    lean_dec(v_fst_3768_);
                    lean_dec_ref(v_x_3755_);
                    lean_dec_ref(v_H_3754_);
                    lean_dec_ref(v___x_3753_);
                    lean_dec_ref(v___x_3752_);
                    lean_dec_ref(v___x_3751_);
                    lean_dec_ref(v___x_3750_);
                    lean_dec_ref(v___x_3749_);
                    lean_dec_ref(v___x_3748_);
                    lean_dec_ref(v___x_3744_);
                    v_a_3834_ = lean_ctor_get(v___x_3783_, 0);
                    v_isSharedCheck_3841_ = (!lean_is_exclusive(v___x_3783_)) as u8;
                    if v_isSharedCheck_3841_ == 0 {
                        v___x_3836_ = v___x_3783_;
                        v_isShared_3837_ = v_isSharedCheck_3841_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3834_);
                        lean_dec(v___x_3783_);
                        v___x_3836_ = lean_box(0);
                        v_isShared_3837_ = v_isSharedCheck_3841_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v_u_3794_ = lean_ctor_get(v_fst_3772_, 0);
                v_00_u03c3s_3795_ = lean_ctor_get(v_fst_3772_, 1);
                v_target_3796_ = lean_ctor_get(v_fst_3772_, 3);
                v_isSharedCheck_3823_ = (!lean_is_exclusive(v_fst_3772_)) as u8;
                if v_isSharedCheck_3823_ == 0 {
                    v_unused_3824_ = lean_ctor_get(v_fst_3772_, 2);
                    lean_dec(v_unused_3824_);
                    v___x_3798_ = v_fst_3772_;
                    v_isShared_3799_ = v_isSharedCheck_3823_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_target_3796_);
                    lean_inc(v_00_u03c3s_3795_);
                    lean_inc(v_u_3794_);
                    lean_dec(v_fst_3772_);
                    v___x_3798_ = lean_box(0);
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
                v___x_3803_ = lean_box(0);
                if v_isShared_3771_ == 0 {
                    lean_ctor_set_tag(v___x_3770_, 1);
                    lean_ctor_set(v___x_3770_, 1, v___x_3803_);
                    lean_ctor_set(v___x_3770_, 0, v_a_3784_);
                    v___x_3805_ = v___x_3770_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3784_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 1, v___x_3803_);
                    v___x_3805_ = v_reuseFailAlloc_3822_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_inc_n(v_u_3794_, 2);
                v___x_3806_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3806_, 0, v_u_3794_);
                lean_ctor_set(v___x_3806_, 1, v___x_3805_);
                v___x_3807_ = l_Lean_mkConst(v___x_3802_, v___x_3806_);
                lean_inc_ref(v_target_3796_);
                lean_inc(v_fst_3779_);
                lean_inc_ref(v___x_3752_);
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
                    lean_ctor_set(v___x_3798_, 2, v___x_3809_);
                    v___x_3811_ = v___x_3798_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_u_3794_);
                    lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_00_u03c3s_3795_);
                    lean_ctor_set(v_reuseFailAlloc_3821_, 2, v___x_3809_);
                    lean_ctor_set(v_reuseFailAlloc_3821_, 3, v_target_3796_);
                    v___x_3811_ = v_reuseFailAlloc_3821_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3782_ == 0 {
                    lean_ctor_set(v___x_3781_, 1, v___x_3808_);
                    lean_ctor_set(v___x_3781_, 0, v___x_3811_);
                    v___x_3813_ = v___x_3781_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3811_);
                    lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___x_3808_);
                    v___x_3813_ = v_reuseFailAlloc_3820_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3776_ == 0 {
                    lean_ctor_set(v___x_3775_, 1, v___x_3813_);
                    lean_ctor_set(v___x_3775_, 0, v_fst_3768_);
                    v___x_3815_ = v___x_3775_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_fst_3768_);
                    lean_ctor_set(v_reuseFailAlloc_3819_, 1, v___x_3813_);
                    v___x_3815_ = v_reuseFailAlloc_3819_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3793_ == 0 {
                    lean_ctor_set(v___x_3792_, 0, v___x_3815_);
                    v___x_3817_ = v___x_3792_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
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
                    v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
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
                    v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
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
                    v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
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
                    v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3862_: *mut LeanObject = *_args.add(0);
    let mut v_snd_3863_: *mut LeanObject = *_args.add(1);
    let mut v_k_3864_: *mut LeanObject = *_args.add(2);
    let mut v___x_3865_: *mut LeanObject = *_args.add(3);
    let mut v___x_3866_: *mut LeanObject = *_args.add(4);
    let mut v___x_3867_: *mut LeanObject = *_args.add(5);
    let mut v___x_3868_: *mut LeanObject = *_args.add(6);
    let mut v___x_3869_: *mut LeanObject = *_args.add(7);
    let mut v___x_3870_: *mut LeanObject = *_args.add(8);
    let mut v___x_3871_: *mut LeanObject = *_args.add(9);
    let mut v_H_3872_: *mut LeanObject = *_args.add(10);
    let mut v_x_3873_: *mut LeanObject = *_args.add(11);
    let mut v___y_3874_: *mut LeanObject = *_args.add(12);
    let mut v___y_3875_: *mut LeanObject = *_args.add(13);
    let mut v___y_3876_: *mut LeanObject = *_args.add(14);
    let mut v___y_3877_: *mut LeanObject = *_args.add(15);
    let mut v___y_3878_: *mut LeanObject = *_args.add(16);
    let mut v___x_2315__boxed_3879_: u8 = 0;
    let mut v_res_3880_: *mut LeanObject = core::ptr::null_mut();
    v___x_2315__boxed_3879_ = (lean_unbox(v___x_3865_) as u8);
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
    lean_dec(v___y_3877_);
    lean_dec_ref(v___y_3876_);
    lean_dec(v___y_3875_);
    lean_dec_ref(v___y_3874_);
    return v_res_3880_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(
    mut v_k_3881_: *mut LeanObject,
    mut v_b_3882_: *mut LeanObject,
    mut v___y_3883_: *mut LeanObject,
    mut v___y_3884_: *mut LeanObject,
    mut v___y_3885_: *mut LeanObject,
    mut v___y_3886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3886_);
    lean_inc_ref(v___y_3885_);
    lean_inc(v___y_3884_);
    lean_inc_ref(v___y_3883_);
    v___x_3888_ = lean_apply_6(
        v_k_3881_,
        v_b_3882_,
        v___y_3883_,
        v___y_3884_,
        v___y_3885_,
        v___y_3886_,
        lean_box(0),
    );
    return v___x_3888_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_3889_: *mut LeanObject,
    mut v_b_3890_: *mut LeanObject,
    mut v___y_3891_: *mut LeanObject,
    mut v___y_3892_: *mut LeanObject,
    mut v___y_3893_: *mut LeanObject,
    mut v___y_3894_: *mut LeanObject,
    mut v___y_3895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3896_: *mut LeanObject = core::ptr::null_mut();
    v_res_3896_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(v_k_3889_, v_b_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
    lean_dec(v___y_3894_);
    lean_dec_ref(v___y_3893_);
    lean_dec(v___y_3892_);
    lean_dec_ref(v___y_3891_);
    return v_res_3896_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(
    mut v_name_3897_: *mut LeanObject,
    mut v_bi_3898_: u8,
    mut v_type_3899_: *mut LeanObject,
    mut v_k_3900_: *mut LeanObject,
    mut v_kind_3901_: u8,
    mut v___y_3902_: *mut LeanObject,
    mut v___y_3903_: *mut LeanObject,
    mut v___y_3904_: *mut LeanObject,
    mut v___y_3905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3916_: u8 = 0;
    let mut v_a_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3907_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_3907_, 0, v_k_3900_);
                v___x_3908_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_3908_) == 0 {
                    v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
                    v_isSharedCheck_3916_ = (!lean_is_exclusive(v___x_3908_)) as u8;
                    if v_isSharedCheck_3916_ == 0 {
                        v___x_3911_ = v___x_3908_;
                        v_isShared_3912_ = v_isSharedCheck_3916_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3909_);
                        lean_dec(v___x_3908_);
                        v___x_3911_ = lean_box(0);
                        v_isShared_3912_ = v_isSharedCheck_3916_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3917_ = lean_ctor_get(v___x_3908_, 0);
                    v_isSharedCheck_3924_ = (!lean_is_exclusive(v___x_3908_)) as u8;
                    if v_isSharedCheck_3924_ == 0 {
                        v___x_3919_ = v___x_3908_;
                        v_isShared_3920_ = v_isSharedCheck_3924_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3917_);
                        lean_dec(v___x_3908_);
                        v___x_3919_ = lean_box(0);
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
                    v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
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
                    v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
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
    mut v_name_3925_: *mut LeanObject,
    mut v_bi_3926_: *mut LeanObject,
    mut v_type_3927_: *mut LeanObject,
    mut v_k_3928_: *mut LeanObject,
    mut v_kind_3929_: *mut LeanObject,
    mut v___y_3930_: *mut LeanObject,
    mut v___y_3931_: *mut LeanObject,
    mut v___y_3932_: *mut LeanObject,
    mut v___y_3933_: *mut LeanObject,
    mut v___y_3934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3935_: u8 = 0;
    let mut v_kind_boxed_3936_: u8 = 0;
    let mut v_res_3937_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3935_ = (lean_unbox(v_bi_3926_) as u8);
    v_kind_boxed_3936_ = (lean_unbox(v_kind_3929_) as u8);
    v_res_3937_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_3925_, v_bi_boxed_3935_, v_type_3927_, v_k_3928_, v_kind_boxed_3936_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
    lean_dec(v___y_3933_);
    lean_dec_ref(v___y_3932_);
    lean_dec(v___y_3931_);
    lean_dec_ref(v___y_3930_);
    return v_res_3937_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(
    mut v_name_3938_: *mut LeanObject,
    mut v_type_3939_: *mut LeanObject,
    mut v_k_3940_: *mut LeanObject,
    mut v___y_3941_: *mut LeanObject,
    mut v___y_3942_: *mut LeanObject,
    mut v___y_3943_: *mut LeanObject,
    mut v___y_3944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3946_: u8 = 0;
    let mut v___x_3947_: u8 = 0;
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    v___x_3946_ = 0;
    v___x_3947_ = 0;
    v___x_3948_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_3938_, v___x_3946_, v_type_3939_, v_k_3940_, v___x_3947_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
    return v___x_3948_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg___boxed(
    mut v_name_3949_: *mut LeanObject,
    mut v_type_3950_: *mut LeanObject,
    mut v_k_3951_: *mut LeanObject,
    mut v___y_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
    mut v___y_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
    mut v___y_3956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3957_: *mut LeanObject = core::ptr::null_mut();
    v_res_3957_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_3949_, v_type_3950_, v_k_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
    lean_dec(v___y_3955_);
    lean_dec_ref(v___y_3954_);
    lean_dec(v___y_3953_);
    lean_dec_ref(v___y_3952_);
    return v_res_3957_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    v___x_3965_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2;
    v___x_3966_ = l_Lean_stringToMessageData(v___x_3965_);
    return v___x_3966_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(
    mut v_H_3967_: *mut LeanObject,
    mut v_name_3968_: *mut LeanObject,
    mut v_k_3969_: *mut LeanObject,
    mut v_a_3970_: *mut LeanObject,
    mut v_a_3971_: *mut LeanObject,
    mut v_a_3972_: *mut LeanObject,
    mut v_a_3973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: u8 = 0;
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4002_: u8 = 0;
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4005_: *mut LeanObject = core::ptr::null_mut();
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
                v___x_3981_ = lean_unsigned_to_nat(3);
                v___x_3982_ = l_Lean_Expr_isAppOfArity(v___x_3975_, v___x_3980_, v___x_3981_);
                if v___x_3982_ == 0 {
                    lean_dec_ref(v___x_3975_);
                    lean_dec_ref(v_k_3969_);
                    lean_dec(v_name_3968_);
                    v___x_3983_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3,
                    );
                    v___x_3984_ = l_Lean_MessageData_ofExpr(v_H_3967_);
                    v___x_3985_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3985_, 0, v___x_3983_);
                    lean_ctor_set(v___x_3985_, 1, v___x_3984_);
                    v___x_3986_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_3985_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
                    return v___x_3986_;
                } else {
                    v___x_3987_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(
                        v_name_3968_,
                        v_a_3972_,
                        v_a_3973_,
                    );
                    if lean_obj_tag(v___x_3987_) == 0 {
                        v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
                        lean_inc(v_a_3988_);
                        lean_dec_ref_known(v___x_3987_, 1);
                        v_fst_3989_ = lean_ctor_get(v_a_3988_, 0);
                        lean_inc(v_fst_3989_);
                        v_snd_3990_ = lean_ctor_get(v_a_3988_, 1);
                        lean_inc(v_snd_3990_);
                        lean_dec(v_a_3988_);
                        v___x_3991_ = l_Lean_Expr_appFn_x21(v___x_3975_);
                        v___x_3992_ = l_Lean_Expr_appFn_x21(v___x_3991_);
                        v___x_3993_ = l_Lean_Expr_appArg_x21(v___x_3992_);
                        lean_dec_ref(v___x_3992_);
                        v___x_3994_ = l_Lean_Expr_appArg_x21(v___x_3991_);
                        lean_dec_ref(v___x_3991_);
                        v___x_3995_ = l_Lean_Expr_appArg_x21(v___x_3975_);
                        lean_dec_ref(v___x_3975_);
                        v___x_3996_ = lean_box((v___x_3982_) as usize);
                        lean_inc_ref(v___x_3993_);
                        v___f_3997_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            17,
                            11,
                        );
                        lean_closure_set(v___f_3997_, 0, v___x_3993_);
                        lean_closure_set(v___f_3997_, 1, v_snd_3990_);
                        lean_closure_set(v___f_3997_, 2, v_k_3969_);
                        lean_closure_set(v___f_3997_, 3, v___x_3996_);
                        lean_closure_set(v___f_3997_, 4, v___x_3976_);
                        lean_closure_set(v___f_3997_, 5, v___x_3977_);
                        lean_closure_set(v___f_3997_, 6, v___x_3978_);
                        lean_closure_set(v___f_3997_, 7, v___x_3979_);
                        lean_closure_set(v___f_3997_, 8, v___x_3994_);
                        lean_closure_set(v___f_3997_, 9, v___x_3995_);
                        lean_closure_set(v___f_3997_, 10, v_H_3967_);
                        v___x_3998_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_3989_, v___x_3993_, v___f_3997_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
                        return v___x_3998_;
                    } else {
                        lean_dec_ref(v___x_3975_);
                        lean_dec_ref(v_k_3969_);
                        lean_dec_ref(v_H_3967_);
                        v_a_3999_ = lean_ctor_get(v___x_3987_, 0);
                        v_isSharedCheck_4006_ = (!lean_is_exclusive(v___x_3987_)) as u8;
                        if v_isSharedCheck_4006_ == 0 {
                            v___x_4001_ = v___x_3987_;
                            v_isShared_4002_ = v_isSharedCheck_4006_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3999_);
                            lean_dec(v___x_3987_);
                            v___x_4001_ = lean_box(0);
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
                    v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
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
    mut v_H_4007_: *mut LeanObject,
    mut v_name_4008_: *mut LeanObject,
    mut v_k_4009_: *mut LeanObject,
    mut v_a_4010_: *mut LeanObject,
    mut v_a_4011_: *mut LeanObject,
    mut v_a_4012_: *mut LeanObject,
    mut v_a_4013_: *mut LeanObject,
    mut v_a_4014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4015_: *mut LeanObject = core::ptr::null_mut();
    v_res_4015_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(
        v_H_4007_,
        v_name_4008_,
        v_k_4009_,
        v_a_4010_,
        v_a_4011_,
        v_a_4012_,
        v_a_4013_,
    );
    lean_dec(v_a_4013_);
    lean_dec_ref(v_a_4012_);
    lean_dec(v_a_4011_);
    lean_dec_ref(v_a_4010_);
    return v_res_4015_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(
    mut v_00_u03b1_4016_: *mut LeanObject,
    mut v_H_4017_: *mut LeanObject,
    mut v_name_4018_: *mut LeanObject,
    mut v_k_4019_: *mut LeanObject,
    mut v_a_4020_: *mut LeanObject,
    mut v_a_4021_: *mut LeanObject,
    mut v_a_4022_: *mut LeanObject,
    mut v_a_4023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4026_: *mut LeanObject,
    mut v_H_4027_: *mut LeanObject,
    mut v_name_4028_: *mut LeanObject,
    mut v_k_4029_: *mut LeanObject,
    mut v_a_4030_: *mut LeanObject,
    mut v_a_4031_: *mut LeanObject,
    mut v_a_4032_: *mut LeanObject,
    mut v_a_4033_: *mut LeanObject,
    mut v_a_4034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4035_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4033_);
    lean_dec_ref(v_a_4032_);
    lean_dec(v_a_4031_);
    lean_dec_ref(v_a_4030_);
    return v_res_4035_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(
    mut v_00_u03b1_4036_: *mut LeanObject,
    mut v_name_4037_: *mut LeanObject,
    mut v_bi_4038_: u8,
    mut v_type_4039_: *mut LeanObject,
    mut v_k_4040_: *mut LeanObject,
    mut v_kind_4041_: u8,
    mut v___y_4042_: *mut LeanObject,
    mut v___y_4043_: *mut LeanObject,
    mut v___y_4044_: *mut LeanObject,
    mut v___y_4045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    v___x_4047_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_4037_, v_bi_4038_, v_type_4039_, v_k_4040_, v_kind_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
    return v___x_4047_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___boxed(
    mut v_00_u03b1_4048_: *mut LeanObject,
    mut v_name_4049_: *mut LeanObject,
    mut v_bi_4050_: *mut LeanObject,
    mut v_type_4051_: *mut LeanObject,
    mut v_k_4052_: *mut LeanObject,
    mut v_kind_4053_: *mut LeanObject,
    mut v___y_4054_: *mut LeanObject,
    mut v___y_4055_: *mut LeanObject,
    mut v___y_4056_: *mut LeanObject,
    mut v___y_4057_: *mut LeanObject,
    mut v___y_4058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_4059_: u8 = 0;
    let mut v_kind_boxed_4060_: u8 = 0;
    let mut v_res_4061_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_4059_ = (lean_unbox(v_bi_4050_) as u8);
    v_kind_boxed_4060_ = (lean_unbox(v_kind_4053_) as u8);
    v_res_4061_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(v_00_u03b1_4048_, v_name_4049_, v_bi_boxed_4059_, v_type_4051_, v_k_4052_, v_kind_boxed_4060_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
    lean_dec(v___y_4057_);
    lean_dec_ref(v___y_4056_);
    lean_dec(v___y_4055_);
    lean_dec_ref(v___y_4054_);
    return v_res_4061_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(
    mut v_00_u03b1_4062_: *mut LeanObject,
    mut v_name_4063_: *mut LeanObject,
    mut v_type_4064_: *mut LeanObject,
    mut v_k_4065_: *mut LeanObject,
    mut v___y_4066_: *mut LeanObject,
    mut v___y_4067_: *mut LeanObject,
    mut v___y_4068_: *mut LeanObject,
    mut v___y_4069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    v___x_4071_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_4063_, v_type_4064_, v_k_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
    return v___x_4071_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___boxed(
    mut v_00_u03b1_4072_: *mut LeanObject,
    mut v_name_4073_: *mut LeanObject,
    mut v_type_4074_: *mut LeanObject,
    mut v_k_4075_: *mut LeanObject,
    mut v___y_4076_: *mut LeanObject,
    mut v___y_4077_: *mut LeanObject,
    mut v___y_4078_: *mut LeanObject,
    mut v___y_4079_: *mut LeanObject,
    mut v___y_4080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4081_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4079_);
    lean_dec_ref(v___y_4078_);
    lean_dec(v___y_4077_);
    lean_dec_ref(v___y_4076_);
    return v_res_4081_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    v___x_4082_ = lean_box(0);
    v___x_4083_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_4084_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4084_, 0, v___x_4083_);
    lean_ctor_set(v___x_4084_, 1, v___x_4082_);
    return v___x_4084_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    v___x_4086_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
    v___x_4087_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4087_, 0, v___x_4086_);
    return v___x_4087_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___boxed(
    mut v___y_4088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4089_: *mut LeanObject = core::ptr::null_mut();
    v_res_4089_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
    return v_res_4089_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(
    mut v_00_u03b1_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
    mut v___y_4092_: *mut LeanObject,
    mut v___y_4093_: *mut LeanObject,
    mut v___y_4094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    v___x_4096_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
    return v___x_4096_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___boxed(
    mut v_00_u03b1_4097_: *mut LeanObject,
    mut v___y_4098_: *mut LeanObject,
    mut v___y_4099_: *mut LeanObject,
    mut v___y_4100_: *mut LeanObject,
    mut v___y_4101_: *mut LeanObject,
    mut v___y_4102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4103_: *mut LeanObject = core::ptr::null_mut();
    v_res_4103_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(v_00_u03b1_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
    lean_dec(v___y_4101_);
    lean_dec_ref(v___y_4100_);
    lean_dec(v___y_4099_);
    lean_dec_ref(v___y_4098_);
    return v_res_4103_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(
    mut v___y_4104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4112_: u8 = 0;
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v_r_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4136_: u8 = 0;
    let mut v_unused_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4106_ = lean_st_ref_get(v___y_4104_);
                v_ngen_4107_ = lean_ctor_get(v___x_4106_, 2);
                lean_inc_ref(v_ngen_4107_);
                lean_dec(v___x_4106_);
                v_namePrefix_4108_ = lean_ctor_get(v_ngen_4107_, 0);
                v_idx_4109_ = lean_ctor_get(v_ngen_4107_, 1);
                v_isSharedCheck_4138_ = (!lean_is_exclusive(v_ngen_4107_)) as u8;
                if v_isSharedCheck_4138_ == 0 {
                    v___x_4111_ = v_ngen_4107_;
                    v_isShared_4112_ = v_isSharedCheck_4138_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_4109_);
                    lean_inc(v_namePrefix_4108_);
                    lean_dec(v_ngen_4107_);
                    v___x_4111_ = lean_box(0);
                    v_isShared_4112_ = v_isSharedCheck_4138_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4113_ = lean_st_ref_take(v___y_4104_);
                v_env_4114_ = lean_ctor_get(v___x_4113_, 0);
                v_nextMacroScope_4115_ = lean_ctor_get(v___x_4113_, 1);
                v_auxDeclNGen_4116_ = lean_ctor_get(v___x_4113_, 3);
                v_traceState_4117_ = lean_ctor_get(v___x_4113_, 4);
                v_cache_4118_ = lean_ctor_get(v___x_4113_, 5);
                v_messages_4119_ = lean_ctor_get(v___x_4113_, 6);
                v_infoState_4120_ = lean_ctor_get(v___x_4113_, 7);
                v_snapshotTasks_4121_ = lean_ctor_get(v___x_4113_, 8);
                v_isSharedCheck_4136_ = (!lean_is_exclusive(v___x_4113_)) as u8;
                if v_isSharedCheck_4136_ == 0 {
                    v_unused_4137_ = lean_ctor_get(v___x_4113_, 2);
                    lean_dec(v_unused_4137_);
                    v___x_4123_ = v___x_4113_;
                    v_isShared_4124_ = v_isSharedCheck_4136_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4121_);
                    lean_inc(v_infoState_4120_);
                    lean_inc(v_messages_4119_);
                    lean_inc(v_cache_4118_);
                    lean_inc(v_traceState_4117_);
                    lean_inc(v_auxDeclNGen_4116_);
                    lean_inc(v_nextMacroScope_4115_);
                    lean_inc(v_env_4114_);
                    lean_dec(v___x_4113_);
                    v___x_4123_ = lean_box(0);
                    v_isShared_4124_ = v_isSharedCheck_4136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_idx_4109_);
                lean_inc(v_namePrefix_4108_);
                v_r_4125_ = l_Lean_Name_num___override(v_namePrefix_4108_, v_idx_4109_);
                v___x_4126_ = lean_unsigned_to_nat(1);
                v___x_4127_ = lean_nat_add(v_idx_4109_, v___x_4126_);
                lean_dec(v_idx_4109_);
                if v_isShared_4112_ == 0 {
                    lean_ctor_set(v___x_4111_, 1, v___x_4127_);
                    v___x_4129_ = v___x_4111_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_namePrefix_4108_);
                    lean_ctor_set(v_reuseFailAlloc_4135_, 1, v___x_4127_);
                    v___x_4129_ = v_reuseFailAlloc_4135_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4124_ == 0 {
                    lean_ctor_set(v___x_4123_, 2, v___x_4129_);
                    v___x_4131_ = v___x_4123_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_env_4114_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 1, v_nextMacroScope_4115_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 2, v___x_4129_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 3, v_auxDeclNGen_4116_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 4, v_traceState_4117_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 5, v_cache_4118_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 6, v_messages_4119_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 7, v_infoState_4120_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 8, v_snapshotTasks_4121_);
                    v___x_4131_ = v_reuseFailAlloc_4134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4132_ = lean_st_ref_set(v___y_4104_, v___x_4131_);
                v___x_4133_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4133_, 0, v_r_4125_);
                return v___x_4133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg___boxed(
    mut v___y_4139_: *mut LeanObject,
    mut v___y_4140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4141_: *mut LeanObject = core::ptr::null_mut();
    v_res_4141_ =
        l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(
            v___y_4139_,
        );
    lean_dec(v___y_4139_);
    return v_res_4141_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(
    mut v___y_4142_: *mut LeanObject,
    mut v___y_4143_: *mut LeanObject,
    mut v___y_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    v___x_4147_ =
        l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(
            v___y_4145_,
        );
    return v___x_4147_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___boxed(
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
    mut v___y_4150_: *mut LeanObject,
    mut v___y_4151_: *mut LeanObject,
    mut v___y_4152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4153_: *mut LeanObject = core::ptr::null_mut();
    v_res_4153_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(
        v___y_4148_,
        v___y_4149_,
        v___y_4150_,
        v___y_4151_,
    );
    lean_dec(v___y_4151_);
    lean_dec_ref(v___y_4150_);
    lean_dec(v___y_4149_);
    lean_dec_ref(v___y_4148_);
    return v_res_4153_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(
    mut v_u_4162_: *mut LeanObject,
    mut v_00_u03c3s_4163_: *mut LeanObject,
    mut v_H_u2081_x27_4164_: *mut LeanObject,
    mut v_k_4165_: *mut LeanObject,
    mut v_H_u2082_x27_4166_: *mut LeanObject,
    mut v___y_4167_: *mut LeanObject,
    mut v___y_4168_: *mut LeanObject,
    mut v___y_4169_: *mut LeanObject,
    mut v___y_4170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4177_: u8 = 0;
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4184_: u8 = 0;
    let mut v_fst_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4194_: u8 = 0;
    let mut v_fst_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4198_: u8 = 0;
    let mut v_u_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4204_: u8 = 0;
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut v_unused_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4231_: u8 = 0;
    let mut v_unused_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_a_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4237_: u8 = 0;
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut v_isSharedCheck_4242_: u8 = 0;
    let mut v_isSharedCheck_4243_: u8 = 0;
    let mut v_a_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4247_: u8 = 0;
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4251_: u8 = 0;
    let mut v_isSharedCheck_4252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_H_u2082_x27_4166_);
                lean_inc_ref(v_H_u2081_x27_4164_);
                lean_inc_ref(v_00_u03c3s_4163_);
                lean_inc(v_u_4162_);
                v___x_4172_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                    v_u_4162_,
                    v_00_u03c3s_4163_,
                    v_H_u2081_x27_4164_,
                    v_H_u2082_x27_4166_,
                );
                v_fst_4173_ = lean_ctor_get(v___x_4172_, 0);
                v_snd_4174_ = lean_ctor_get(v___x_4172_, 1);
                v_isSharedCheck_4252_ = (!lean_is_exclusive(v___x_4172_)) as u8;
                if v_isSharedCheck_4252_ == 0 {
                    v___x_4176_ = v___x_4172_;
                    v_isShared_4177_ = v_isSharedCheck_4252_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_4174_);
                    lean_inc(v_fst_4173_);
                    lean_dec(v___x_4172_);
                    v___x_4176_ = lean_box(0);
                    v_isShared_4177_ = v_isSharedCheck_4252_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v___y_4170_);
                lean_inc_ref(v___y_4169_);
                lean_inc(v___y_4168_);
                lean_inc_ref(v___y_4167_);
                lean_inc(v_fst_4173_);
                v___x_4178_ = lean_apply_6(
                    v_k_4165_,
                    v_fst_4173_,
                    v___y_4167_,
                    v___y_4168_,
                    v___y_4169_,
                    v___y_4170_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4178_) == 0 {
                    v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
                    lean_inc(v_a_4179_);
                    lean_dec_ref_known(v___x_4178_, 1);
                    v_snd_4180_ = lean_ctor_get(v_a_4179_, 1);
                    v_fst_4181_ = lean_ctor_get(v_a_4179_, 0);
                    v_isSharedCheck_4243_ = (!lean_is_exclusive(v_a_4179_)) as u8;
                    if v_isSharedCheck_4243_ == 0 {
                        v___x_4183_ = v_a_4179_;
                        v_isShared_4184_ = v_isSharedCheck_4243_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_4180_);
                        lean_inc(v_fst_4181_);
                        lean_dec(v_a_4179_);
                        v___x_4183_ = lean_box(0);
                        v_isShared_4184_ = v_isSharedCheck_4243_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4176_);
                    lean_dec(v_snd_4174_);
                    lean_dec(v_fst_4173_);
                    lean_dec_ref(v_H_u2082_x27_4166_);
                    lean_dec_ref(v_H_u2081_x27_4164_);
                    lean_dec_ref(v_00_u03c3s_4163_);
                    lean_dec(v_u_4162_);
                    v_a_4244_ = lean_ctor_get(v___x_4178_, 0);
                    v_isSharedCheck_4251_ = (!lean_is_exclusive(v___x_4178_)) as u8;
                    if v_isSharedCheck_4251_ == 0 {
                        v___x_4246_ = v___x_4178_;
                        v_isShared_4247_ = v_isSharedCheck_4251_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4244_);
                        lean_dec(v___x_4178_);
                        v___x_4246_ = lean_box(0);
                        v_isShared_4247_ = v_isSharedCheck_4251_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_4185_ = lean_ctor_get(v_snd_4180_, 0);
                v_snd_4186_ = lean_ctor_get(v_snd_4180_, 1);
                v_isSharedCheck_4242_ = (!lean_is_exclusive(v_snd_4180_)) as u8;
                if v_isSharedCheck_4242_ == 0 {
                    v___x_4188_ = v_snd_4180_;
                    v_isShared_4189_ = v_isSharedCheck_4242_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_4186_);
                    lean_inc(v_fst_4185_);
                    lean_dec(v_snd_4180_);
                    v___x_4188_ = lean_box(0);
                    v_isShared_4189_ = v_isSharedCheck_4242_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_fst_4185_);
                v___x_4190_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_4185_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
                if lean_obj_tag(v___x_4190_) == 0 {
                    v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
                    v_isSharedCheck_4233_ = (!lean_is_exclusive(v___x_4190_)) as u8;
                    if v_isSharedCheck_4233_ == 0 {
                        v___x_4193_ = v___x_4190_;
                        v_isShared_4194_ = v_isSharedCheck_4233_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4191_);
                        lean_dec(v___x_4190_);
                        v___x_4193_ = lean_box(0);
                        v_isShared_4194_ = v_isSharedCheck_4233_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4188_);
                    lean_dec(v_snd_4186_);
                    lean_dec(v_fst_4185_);
                    lean_del_object(v___x_4183_);
                    lean_dec(v_fst_4181_);
                    lean_del_object(v___x_4176_);
                    lean_dec(v_snd_4174_);
                    lean_dec(v_fst_4173_);
                    lean_dec_ref(v_H_u2082_x27_4166_);
                    lean_dec_ref(v_H_u2081_x27_4164_);
                    lean_dec_ref(v_00_u03c3s_4163_);
                    lean_dec(v_u_4162_);
                    v_a_4234_ = lean_ctor_get(v___x_4190_, 0);
                    v_isSharedCheck_4241_ = (!lean_is_exclusive(v___x_4190_)) as u8;
                    if v_isSharedCheck_4241_ == 0 {
                        v___x_4236_ = v___x_4190_;
                        v_isShared_4237_ = v_isSharedCheck_4241_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_4234_);
                        lean_dec(v___x_4190_);
                        v___x_4236_ = lean_box(0);
                        v_isShared_4237_ = v_isSharedCheck_4241_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_4195_ = lean_ctor_get(v_a_4191_, 0);
                v_isSharedCheck_4231_ = (!lean_is_exclusive(v_a_4191_)) as u8;
                if v_isSharedCheck_4231_ == 0 {
                    v_unused_4232_ = lean_ctor_get(v_a_4191_, 1);
                    lean_dec(v_unused_4232_);
                    v___x_4197_ = v_a_4191_;
                    v_isShared_4198_ = v_isSharedCheck_4231_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_fst_4195_);
                    lean_dec(v_a_4191_);
                    v___x_4197_ = lean_box(0);
                    v_isShared_4198_ = v_isSharedCheck_4231_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_u_4199_ = lean_ctor_get(v_fst_4185_, 0);
                v_00_u03c3s_4200_ = lean_ctor_get(v_fst_4185_, 1);
                v_target_4201_ = lean_ctor_get(v_fst_4185_, 3);
                v_isSharedCheck_4229_ = (!lean_is_exclusive(v_fst_4185_)) as u8;
                if v_isSharedCheck_4229_ == 0 {
                    v_unused_4230_ = lean_ctor_get(v_fst_4185_, 2);
                    lean_dec(v_unused_4230_);
                    v___x_4203_ = v_fst_4185_;
                    v_isShared_4204_ = v_isSharedCheck_4229_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_target_4201_);
                    lean_inc(v_00_u03c3s_4200_);
                    lean_inc(v_u_4199_);
                    lean_dec(v_fst_4185_);
                    v___x_4203_ = lean_box(0);
                    v_isShared_4204_ = v_isSharedCheck_4229_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4205_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1;
                v___x_4206_ = lean_box(0);
                lean_inc(v_u_4162_);
                if v_isShared_4177_ == 0 {
                    lean_ctor_set_tag(v___x_4176_, 1);
                    lean_ctor_set(v___x_4176_, 1, v___x_4206_);
                    lean_ctor_set(v___x_4176_, 0, v_u_4162_);
                    v___x_4208_ = v___x_4176_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_u_4162_);
                    lean_ctor_set(v_reuseFailAlloc_4228_, 1, v___x_4206_);
                    v___x_4208_ = v_reuseFailAlloc_4228_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4209_ = l_Lean_mkConst(v___x_4205_, v___x_4208_);
                lean_inc_ref(v_target_4201_);
                lean_inc_ref(v_H_u2082_x27_4166_);
                lean_inc_ref(v_H_u2081_x27_4164_);
                lean_inc_n(v_fst_4195_, 2);
                lean_inc_ref_n(v_00_u03c3s_4163_, 2);
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
                lean_inc(v_u_4162_);
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
                    lean_ctor_set(v___x_4203_, 2, v___x_4212_);
                    v___x_4214_ = v___x_4203_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_u_4199_);
                    lean_ctor_set(v_reuseFailAlloc_4227_, 1, v_00_u03c3s_4200_);
                    lean_ctor_set(v_reuseFailAlloc_4227_, 2, v___x_4212_);
                    lean_ctor_set(v_reuseFailAlloc_4227_, 3, v_target_4201_);
                    v___x_4214_ = v_reuseFailAlloc_4227_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4198_ == 0 {
                    lean_ctor_set(v___x_4197_, 1, v_fst_4195_);
                    lean_ctor_set(v___x_4197_, 0, v_fst_4181_);
                    v___x_4216_ = v___x_4197_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_fst_4181_);
                    lean_ctor_set(v_reuseFailAlloc_4226_, 1, v_fst_4195_);
                    v___x_4216_ = v_reuseFailAlloc_4226_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4189_ == 0 {
                    lean_ctor_set(v___x_4188_, 1, v___x_4210_);
                    lean_ctor_set(v___x_4188_, 0, v___x_4214_);
                    v___x_4218_ = v___x_4188_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4214_);
                    lean_ctor_set(v_reuseFailAlloc_4225_, 1, v___x_4210_);
                    v___x_4218_ = v_reuseFailAlloc_4225_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4184_ == 0 {
                    lean_ctor_set(v___x_4183_, 1, v___x_4218_);
                    lean_ctor_set(v___x_4183_, 0, v___x_4216_);
                    v___x_4220_ = v___x_4183_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4216_);
                    lean_ctor_set(v_reuseFailAlloc_4224_, 1, v___x_4218_);
                    v___x_4220_ = v_reuseFailAlloc_4224_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4194_ == 0 {
                    lean_ctor_set(v___x_4193_, 0, v___x_4220_);
                    v___x_4222_ = v___x_4193_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4220_);
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
                    v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
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
                    v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
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
    mut v_u_4253_: *mut LeanObject,
    mut v_00_u03c3s_4254_: *mut LeanObject,
    mut v_H_u2081_x27_4255_: *mut LeanObject,
    mut v_k_4256_: *mut LeanObject,
    mut v_H_u2082_x27_4257_: *mut LeanObject,
    mut v___y_4258_: *mut LeanObject,
    mut v___y_4259_: *mut LeanObject,
    mut v___y_4260_: *mut LeanObject,
    mut v___y_4261_: *mut LeanObject,
    mut v___y_4262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4263_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4261_);
    lean_dec_ref(v___y_4260_);
    lean_dec(v___y_4259_);
    lean_dec_ref(v___y_4258_);
    return v_res_4263_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(
    mut v_a_4266_: *mut LeanObject,
    mut v_snd_4267_: *mut LeanObject,
    mut v_k_4268_: *mut LeanObject,
    mut v___x_4269_: *mut LeanObject,
    mut v___x_4270_: *mut LeanObject,
    mut v___x_4271_: *mut LeanObject,
    mut v___x_4272_: *mut LeanObject,
    mut v___x_4273_: *mut LeanObject,
    mut v_00_u03c3s_4274_: *mut LeanObject,
    mut v_hyp_4275_: *mut LeanObject,
    mut v_a_4276_: *mut LeanObject,
    mut v_a_4277_: *mut LeanObject,
    mut v_h_4278_: *mut LeanObject,
    mut v___y_4279_: *mut LeanObject,
    mut v___y_4280_: *mut LeanObject,
    mut v___y_4281_: *mut LeanObject,
    mut v___y_4282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: u8 = 0;
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4294_: u8 = 0;
    let mut v_fst_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4299_: u8 = 0;
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: u8 = 0;
    let mut v___x_4304_: u8 = 0;
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4309_: u8 = 0;
    let mut v_u_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prf_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goal_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4335_: u8 = 0;
    let mut v_isSharedCheck_4336_: u8 = 0;
    let mut v_a_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4340_: u8 = 0;
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4344_: u8 = 0;
    let mut v_isSharedCheck_4345_: u8 = 0;
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v_a_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4350_: u8 = 0;
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_4284_ = lean_ctor_get(v___y_4279_, 2);
                lean_inc_ref(v_a_4266_);
                v___x_4285_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4285_, 0, v_a_4266_);
                v___x_4286_ = 0;
                lean_inc_ref(v_h_4278_);
                lean_inc_ref(v_lctx_4284_);
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
                if lean_obj_tag(v___x_4287_) == 0 {
                    lean_dec_ref_known(v___x_4287_, 1);
                    lean_inc(v___y_4282_);
                    lean_inc_ref(v___y_4281_);
                    lean_inc(v___y_4280_);
                    lean_inc_ref(v___y_4279_);
                    lean_inc_ref(v_h_4278_);
                    lean_inc_ref(v_a_4266_);
                    v___x_4288_ = lean_apply_7(
                        v_k_4268_,
                        v_a_4266_,
                        v_h_4278_,
                        v___y_4279_,
                        v___y_4280_,
                        v___y_4281_,
                        v___y_4282_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4288_) == 0 {
                        v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
                        lean_inc(v_a_4289_);
                        lean_dec_ref_known(v___x_4288_, 1);
                        v_snd_4290_ = lean_ctor_get(v_a_4289_, 1);
                        v_fst_4291_ = lean_ctor_get(v_a_4289_, 0);
                        v_isSharedCheck_4346_ = (!lean_is_exclusive(v_a_4289_)) as u8;
                        if v_isSharedCheck_4346_ == 0 {
                            v___x_4293_ = v_a_4289_;
                            v_isShared_4294_ = v_isSharedCheck_4346_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_4290_);
                            lean_inc(v_fst_4291_);
                            lean_dec(v_a_4289_);
                            v___x_4293_ = lean_box(0);
                            v_isShared_4294_ = v_isSharedCheck_4346_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_h_4278_);
                        lean_dec(v_a_4277_);
                        lean_dec_ref(v_a_4276_);
                        lean_dec_ref(v_hyp_4275_);
                        lean_dec_ref(v_00_u03c3s_4274_);
                        lean_dec(v___x_4273_);
                        lean_dec_ref(v___x_4272_);
                        lean_dec_ref(v___x_4271_);
                        lean_dec_ref(v___x_4270_);
                        lean_dec_ref(v___x_4269_);
                        lean_dec_ref(v_a_4266_);
                        return v___x_4288_;
                    }
                } else {
                    lean_dec_ref(v_h_4278_);
                    lean_dec(v_a_4277_);
                    lean_dec_ref(v_a_4276_);
                    lean_dec_ref(v_hyp_4275_);
                    lean_dec_ref(v_00_u03c3s_4274_);
                    lean_dec(v___x_4273_);
                    lean_dec_ref(v___x_4272_);
                    lean_dec_ref(v___x_4271_);
                    lean_dec_ref(v___x_4270_);
                    lean_dec_ref(v___x_4269_);
                    lean_dec_ref(v_k_4268_);
                    lean_dec_ref(v_a_4266_);
                    v_a_4347_ = lean_ctor_get(v___x_4287_, 0);
                    v_isSharedCheck_4354_ = (!lean_is_exclusive(v___x_4287_)) as u8;
                    if v_isSharedCheck_4354_ == 0 {
                        v___x_4349_ = v___x_4287_;
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_4347_);
                        lean_dec(v___x_4287_);
                        v___x_4349_ = lean_box(0);
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4295_ = lean_ctor_get(v_snd_4290_, 0);
                v_snd_4296_ = lean_ctor_get(v_snd_4290_, 1);
                v_isSharedCheck_4345_ = (!lean_is_exclusive(v_snd_4290_)) as u8;
                if v_isSharedCheck_4345_ == 0 {
                    v___x_4298_ = v_snd_4290_;
                    v_isShared_4299_ = v_isSharedCheck_4345_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4296_);
                    lean_inc(v_fst_4295_);
                    lean_dec(v_snd_4290_);
                    v___x_4298_ = lean_box(0);
                    v_isShared_4299_ = v_isSharedCheck_4345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4300_ = lean_unsigned_to_nat(1);
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
                lean_dec_ref(v___x_4302_);
                if lean_obj_tag(v___x_4305_) == 0 {
                    v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
                    v_isSharedCheck_4336_ = (!lean_is_exclusive(v___x_4305_)) as u8;
                    if v_isSharedCheck_4336_ == 0 {
                        v___x_4308_ = v___x_4305_;
                        v_isShared_4309_ = v_isSharedCheck_4336_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4306_);
                        lean_dec(v___x_4305_);
                        v___x_4308_ = lean_box(0);
                        v_isShared_4309_ = v_isSharedCheck_4336_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4298_);
                    lean_dec(v_fst_4295_);
                    lean_del_object(v___x_4293_);
                    lean_dec(v_fst_4291_);
                    lean_dec(v_a_4277_);
                    lean_dec_ref(v_a_4276_);
                    lean_dec_ref(v_hyp_4275_);
                    lean_dec_ref(v_00_u03c3s_4274_);
                    lean_dec(v___x_4273_);
                    lean_dec_ref(v___x_4272_);
                    lean_dec_ref(v___x_4271_);
                    lean_dec_ref(v___x_4270_);
                    lean_dec_ref(v___x_4269_);
                    lean_dec_ref(v_a_4266_);
                    v_a_4337_ = lean_ctor_get(v___x_4305_, 0);
                    v_isSharedCheck_4344_ = (!lean_is_exclusive(v___x_4305_)) as u8;
                    if v_isSharedCheck_4344_ == 0 {
                        v___x_4339_ = v___x_4305_;
                        v_isShared_4340_ = v_isSharedCheck_4344_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4337_);
                        lean_dec(v___x_4305_);
                        v___x_4339_ = lean_box(0);
                        v_isShared_4340_ = v_isSharedCheck_4344_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v_u_4310_ = lean_ctor_get(v_fst_4295_, 0);
                v_00_u03c3s_4311_ = lean_ctor_get(v_fst_4295_, 1);
                v_hyps_4312_ = lean_ctor_get(v_fst_4295_, 2);
                v_target_4313_ = lean_ctor_get(v_fst_4295_, 3);
                v_isSharedCheck_4335_ = (!lean_is_exclusive(v_fst_4295_)) as u8;
                if v_isSharedCheck_4335_ == 0 {
                    v___x_4315_ = v_fst_4295_;
                    v_isShared_4316_ = v_isSharedCheck_4335_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_target_4313_);
                    lean_inc(v_hyps_4312_);
                    lean_inc(v_00_u03c3s_4311_);
                    lean_inc(v_u_4310_);
                    lean_dec(v_fst_4295_);
                    v___x_4315_ = lean_box(0);
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
                lean_inc_ref(v_target_4313_);
                lean_inc_ref(v_hyp_4275_);
                lean_inc_ref(v_hyps_4312_);
                lean_inc_ref(v_00_u03c3s_4274_);
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
                    lean_ctor_set(v___x_4315_, 2, v___x_4322_);
                    v_goal_4324_ = v___x_4315_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_u_4310_);
                    lean_ctor_set(v_reuseFailAlloc_4334_, 1, v_00_u03c3s_4311_);
                    lean_ctor_set(v_reuseFailAlloc_4334_, 2, v___x_4322_);
                    lean_ctor_set(v_reuseFailAlloc_4334_, 3, v_target_4313_);
                    v_goal_4324_ = v_reuseFailAlloc_4334_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4299_ == 0 {
                    lean_ctor_set(v___x_4298_, 1, v_prf_4321_);
                    lean_ctor_set(v___x_4298_, 0, v_goal_4324_);
                    v___x_4326_ = v___x_4298_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_goal_4324_);
                    lean_ctor_set(v_reuseFailAlloc_4333_, 1, v_prf_4321_);
                    v___x_4326_ = v_reuseFailAlloc_4333_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4294_ == 0 {
                    lean_ctor_set(v___x_4293_, 1, v___x_4326_);
                    v___x_4328_ = v___x_4293_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_fst_4291_);
                    lean_ctor_set(v_reuseFailAlloc_4332_, 1, v___x_4326_);
                    v___x_4328_ = v_reuseFailAlloc_4332_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4309_ == 0 {
                    lean_ctor_set(v___x_4308_, 0, v___x_4328_);
                    v___x_4330_ = v___x_4308_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4328_);
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
                    v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
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
                    v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4355_: *mut LeanObject = *_args.add(0);
    let mut v_snd_4356_: *mut LeanObject = *_args.add(1);
    let mut v_k_4357_: *mut LeanObject = *_args.add(2);
    let mut v___x_4358_: *mut LeanObject = *_args.add(3);
    let mut v___x_4359_: *mut LeanObject = *_args.add(4);
    let mut v___x_4360_: *mut LeanObject = *_args.add(5);
    let mut v___x_4361_: *mut LeanObject = *_args.add(6);
    let mut v___x_4362_: *mut LeanObject = *_args.add(7);
    let mut v_00_u03c3s_4363_: *mut LeanObject = *_args.add(8);
    let mut v_hyp_4364_: *mut LeanObject = *_args.add(9);
    let mut v_a_4365_: *mut LeanObject = *_args.add(10);
    let mut v_a_4366_: *mut LeanObject = *_args.add(11);
    let mut v_h_4367_: *mut LeanObject = *_args.add(12);
    let mut v___y_4368_: *mut LeanObject = *_args.add(13);
    let mut v___y_4369_: *mut LeanObject = *_args.add(14);
    let mut v___y_4370_: *mut LeanObject = *_args.add(15);
    let mut v___y_4371_: *mut LeanObject = *_args.add(16);
    let mut v___y_4372_: *mut LeanObject = *_args.add(17);
    let mut v_res_4373_: *mut LeanObject = core::ptr::null_mut();
    v_res_4373_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(v_a_4355_, v_snd_4356_, v_k_4357_, v___x_4358_, v___x_4359_, v___x_4360_, v___x_4361_, v___x_4362_, v_00_u03c3s_4363_, v_hyp_4364_, v_a_4365_, v_a_4366_, v_h_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
    lean_dec(v___y_4371_);
    lean_dec_ref(v___y_4370_);
    lean_dec(v___y_4369_);
    lean_dec_ref(v___y_4368_);
    return v_res_4373_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    v___x_4374_ = lean_box(0);
    v___x_4375_ = l_Lean_mkSort(v___x_4374_);
    return v___x_4375_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    v___x_4376_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0);
    v___x_4377_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4377_, 0, v___x_4376_);
    return v___x_4377_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(
    mut v_00_u03c3s_4385_: *mut LeanObject,
    mut v_hyp_4386_: *mut LeanObject,
    mut v_name_4387_: *mut LeanObject,
    mut v_k_4388_: *mut LeanObject,
    mut v___y_4389_: *mut LeanObject,
    mut v___y_4390_: *mut LeanObject,
    mut v___y_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4422_: u8 = 0;
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut v_a_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4430_: u8 = 0;
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4434_: u8 = 0;
    let mut v_a_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4438_: u8 = 0;
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4442_: u8 = 0;
    let mut v_a_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4446_: u8 = 0;
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4449_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_4394_) == 0 {
                    v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
                    lean_inc(v_a_4395_);
                    lean_dec_ref_known(v___x_4394_, 1);
                    v___x_4396_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
                    v___x_4397_ = 0;
                    v___x_4398_ = lean_box(0);
                    v___x_4399_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_4396_,
                        v___x_4397_,
                        v___x_4398_,
                        v___y_4389_,
                        v___y_4390_,
                        v___y_4391_,
                        v___y_4392_,
                    );
                    if lean_obj_tag(v___x_4399_) == 0 {
                        v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
                        lean_inc_n(v_a_4400_, 2);
                        lean_dec_ref_known(v___x_4399_, 1);
                        v___x_4401_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0;
                        v___x_4402_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_;
                        v___x_4403_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1;
                        v___x_4404_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_;
                        v___x_4405_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3;
                        v___x_4406_ = lean_box(0);
                        lean_inc(v_a_4395_);
                        v___x_4407_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_4407_, 0, v_a_4395_);
                        lean_ctor_set(v___x_4407_, 1, v___x_4406_);
                        lean_inc_ref(v___x_4407_);
                        v___x_4408_ = l_Lean_mkConst(v___x_4405_, v___x_4407_);
                        lean_inc_ref(v_hyp_4386_);
                        lean_inc_ref(v_00_u03c3s_4385_);
                        v___x_4409_ =
                            l_Lean_mkApp3(v___x_4408_, v_00_u03c3s_4385_, v_hyp_4386_, v_a_4400_);
                        v___x_4410_ = lean_box(0);
                        v___x_4411_ = l_Lean_Meta_synthInstance(
                            v___x_4409_,
                            v___x_4410_,
                            v___y_4389_,
                            v___y_4390_,
                            v___y_4391_,
                            v___y_4392_,
                        );
                        if lean_obj_tag(v___x_4411_) == 0 {
                            v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
                            lean_inc(v_a_4412_);
                            lean_dec_ref_known(v___x_4411_, 1);
                            v___x_4413_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(
                                v_name_4387_,
                                v___y_4391_,
                                v___y_4392_,
                            );
                            if lean_obj_tag(v___x_4413_) == 0 {
                                v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
                                lean_inc(v_a_4414_);
                                lean_dec_ref_known(v___x_4413_, 1);
                                v_fst_4415_ = lean_ctor_get(v_a_4414_, 0);
                                lean_inc(v_fst_4415_);
                                v_snd_4416_ = lean_ctor_get(v_a_4414_, 1);
                                lean_inc(v_snd_4416_);
                                lean_dec(v_a_4414_);
                                lean_inc(v_a_4400_);
                                v___f_4417_ = lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 18, 12);
                                lean_closure_set(v___f_4417_, 0, v_a_4400_);
                                lean_closure_set(v___f_4417_, 1, v_snd_4416_);
                                lean_closure_set(v___f_4417_, 2, v_k_4388_);
                                lean_closure_set(v___f_4417_, 3, v___x_4401_);
                                lean_closure_set(v___f_4417_, 4, v___x_4402_);
                                lean_closure_set(v___f_4417_, 5, v___x_4403_);
                                lean_closure_set(v___f_4417_, 6, v___x_4404_);
                                lean_closure_set(v___f_4417_, 7, v___x_4407_);
                                lean_closure_set(v___f_4417_, 8, v_00_u03c3s_4385_);
                                lean_closure_set(v___f_4417_, 9, v_hyp_4386_);
                                lean_closure_set(v___f_4417_, 10, v_a_4412_);
                                lean_closure_set(v___f_4417_, 11, v_a_4395_);
                                v___x_4418_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_4415_, v_a_4400_, v___f_4417_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
                                return v___x_4418_;
                            } else {
                                lean_dec(v_a_4412_);
                                lean_dec_ref_known(v___x_4407_, 2);
                                lean_dec(v_a_4400_);
                                lean_dec(v_a_4395_);
                                lean_dec_ref(v_k_4388_);
                                lean_dec_ref(v_hyp_4386_);
                                lean_dec_ref(v_00_u03c3s_4385_);
                                v_a_4419_ = lean_ctor_get(v___x_4413_, 0);
                                v_isSharedCheck_4426_ = (!lean_is_exclusive(v___x_4413_)) as u8;
                                if v_isSharedCheck_4426_ == 0 {
                                    v___x_4421_ = v___x_4413_;
                                    v_isShared_4422_ = v_isSharedCheck_4426_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_4419_);
                                    lean_dec(v___x_4413_);
                                    v___x_4421_ = lean_box(0);
                                    v_isShared_4422_ = v_isSharedCheck_4426_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v___x_4407_, 2);
                            lean_dec(v_a_4400_);
                            lean_dec(v_a_4395_);
                            lean_dec_ref(v_k_4388_);
                            lean_dec(v_name_4387_);
                            lean_dec_ref(v_hyp_4386_);
                            lean_dec_ref(v_00_u03c3s_4385_);
                            v_a_4427_ = lean_ctor_get(v___x_4411_, 0);
                            v_isSharedCheck_4434_ = (!lean_is_exclusive(v___x_4411_)) as u8;
                            if v_isSharedCheck_4434_ == 0 {
                                v___x_4429_ = v___x_4411_;
                                v_isShared_4430_ = v_isSharedCheck_4434_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4427_);
                                lean_dec(v___x_4411_);
                                v___x_4429_ = lean_box(0);
                                v_isShared_4430_ = v_isSharedCheck_4434_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4395_);
                        lean_dec_ref(v_k_4388_);
                        lean_dec(v_name_4387_);
                        lean_dec_ref(v_hyp_4386_);
                        lean_dec_ref(v_00_u03c3s_4385_);
                        v_a_4435_ = lean_ctor_get(v___x_4399_, 0);
                        v_isSharedCheck_4442_ = (!lean_is_exclusive(v___x_4399_)) as u8;
                        if v_isSharedCheck_4442_ == 0 {
                            v___x_4437_ = v___x_4399_;
                            v_isShared_4438_ = v_isSharedCheck_4442_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4435_);
                            lean_dec(v___x_4399_);
                            v___x_4437_ = lean_box(0);
                            v_isShared_4438_ = v_isSharedCheck_4442_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_k_4388_);
                    lean_dec(v_name_4387_);
                    lean_dec_ref(v_hyp_4386_);
                    lean_dec_ref(v_00_u03c3s_4385_);
                    v_a_4443_ = lean_ctor_get(v___x_4394_, 0);
                    v_isSharedCheck_4450_ = (!lean_is_exclusive(v___x_4394_)) as u8;
                    if v_isSharedCheck_4450_ == 0 {
                        v___x_4445_ = v___x_4394_;
                        v_isShared_4446_ = v_isSharedCheck_4450_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4443_);
                        lean_dec(v___x_4394_);
                        v___x_4445_ = lean_box(0);
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
                    v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
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
                    v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
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
                    v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
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
                    v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
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
    mut v_00_u03c3s_4451_: *mut LeanObject,
    mut v_hyp_4452_: *mut LeanObject,
    mut v_name_4453_: *mut LeanObject,
    mut v_k_4454_: *mut LeanObject,
    mut v___y_4455_: *mut LeanObject,
    mut v___y_4456_: *mut LeanObject,
    mut v___y_4457_: *mut LeanObject,
    mut v___y_4458_: *mut LeanObject,
    mut v___y_4459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4460_: *mut LeanObject = core::ptr::null_mut();
    v_res_4460_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_4451_, v_hyp_4452_, v_name_4453_, v_k_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
    lean_dec(v___y_4458_);
    lean_dec_ref(v___y_4457_);
    lean_dec(v___y_4456_);
    lean_dec_ref(v___y_4455_);
    return v_res_4460_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(
    mut v_u_4469_: *mut LeanObject,
    mut v_00_u03c3s_4470_: *mut LeanObject,
    mut v_k_4471_: *mut LeanObject,
    mut v_x_4472_: *mut LeanObject,
    mut v___h_u03c6_4473_: *mut LeanObject,
    mut v___y_4474_: *mut LeanObject,
    mut v___y_4475_: *mut LeanObject,
    mut v___y_4476_: *mut LeanObject,
    mut v___y_4477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_H_x27_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4486_: u8 = 0;
    let mut v_fst_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4496_: u8 = 0;
    let mut v_fst_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4500_: u8 = 0;
    let mut v_u_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4506_: u8 = 0;
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4526_: u8 = 0;
    let mut v_unused_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut v_unused_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_a_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v_isSharedCheck_4539_: u8 = 0;
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_00_u03c3s_4470_);
                lean_inc(v_u_4469_);
                v_H_x27_4479_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_4469_, v_00_u03c3s_4470_);
                lean_inc(v___y_4477_);
                lean_inc_ref(v___y_4476_);
                lean_inc(v___y_4475_);
                lean_inc_ref(v___y_4474_);
                v___x_4480_ = lean_apply_6(
                    v_k_4471_,
                    v_H_x27_4479_,
                    v___y_4474_,
                    v___y_4475_,
                    v___y_4476_,
                    v___y_4477_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4480_) == 0 {
                    v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
                    lean_inc(v_a_4481_);
                    lean_dec_ref_known(v___x_4480_, 1);
                    v_snd_4482_ = lean_ctor_get(v_a_4481_, 1);
                    v_fst_4483_ = lean_ctor_get(v_a_4481_, 0);
                    v_isSharedCheck_4540_ = (!lean_is_exclusive(v_a_4481_)) as u8;
                    if v_isSharedCheck_4540_ == 0 {
                        v___x_4485_ = v_a_4481_;
                        v_isShared_4486_ = v_isSharedCheck_4540_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4482_);
                        lean_inc(v_fst_4483_);
                        lean_dec(v_a_4481_);
                        v___x_4485_ = lean_box(0);
                        v_isShared_4486_ = v_isSharedCheck_4540_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_00_u03c3s_4470_);
                    lean_dec(v_u_4469_);
                    return v___x_4480_;
                }
            }
            1 => {
                v_fst_4487_ = lean_ctor_get(v_snd_4482_, 0);
                v_snd_4488_ = lean_ctor_get(v_snd_4482_, 1);
                v_isSharedCheck_4539_ = (!lean_is_exclusive(v_snd_4482_)) as u8;
                if v_isSharedCheck_4539_ == 0 {
                    v___x_4490_ = v_snd_4482_;
                    v_isShared_4491_ = v_isSharedCheck_4539_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4488_);
                    lean_inc(v_fst_4487_);
                    lean_dec(v_snd_4482_);
                    v___x_4490_ = lean_box(0);
                    v_isShared_4491_ = v_isSharedCheck_4539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_fst_4487_);
                v___x_4492_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_4487_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
                if lean_obj_tag(v___x_4492_) == 0 {
                    v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
                    v_isSharedCheck_4530_ = (!lean_is_exclusive(v___x_4492_)) as u8;
                    if v_isSharedCheck_4530_ == 0 {
                        v___x_4495_ = v___x_4492_;
                        v_isShared_4496_ = v_isSharedCheck_4530_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4493_);
                        lean_dec(v___x_4492_);
                        v___x_4495_ = lean_box(0);
                        v_isShared_4496_ = v_isSharedCheck_4530_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4490_);
                    lean_dec(v_snd_4488_);
                    lean_dec(v_fst_4487_);
                    lean_del_object(v___x_4485_);
                    lean_dec(v_fst_4483_);
                    lean_dec_ref(v_00_u03c3s_4470_);
                    lean_dec(v_u_4469_);
                    v_a_4531_ = lean_ctor_get(v___x_4492_, 0);
                    v_isSharedCheck_4538_ = (!lean_is_exclusive(v___x_4492_)) as u8;
                    if v_isSharedCheck_4538_ == 0 {
                        v___x_4533_ = v___x_4492_;
                        v_isShared_4534_ = v_isSharedCheck_4538_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_4531_);
                        lean_dec(v___x_4492_);
                        v___x_4533_ = lean_box(0);
                        v_isShared_4534_ = v_isSharedCheck_4538_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_4497_ = lean_ctor_get(v_a_4493_, 0);
                v_isSharedCheck_4528_ = (!lean_is_exclusive(v_a_4493_)) as u8;
                if v_isSharedCheck_4528_ == 0 {
                    v_unused_4529_ = lean_ctor_get(v_a_4493_, 1);
                    lean_dec(v_unused_4529_);
                    v___x_4499_ = v_a_4493_;
                    v_isShared_4500_ = v_isSharedCheck_4528_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_fst_4497_);
                    lean_dec(v_a_4493_);
                    v___x_4499_ = lean_box(0);
                    v_isShared_4500_ = v_isSharedCheck_4528_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_u_4501_ = lean_ctor_get(v_fst_4487_, 0);
                v_00_u03c3s_4502_ = lean_ctor_get(v_fst_4487_, 1);
                v_target_4503_ = lean_ctor_get(v_fst_4487_, 3);
                v_isSharedCheck_4526_ = (!lean_is_exclusive(v_fst_4487_)) as u8;
                if v_isSharedCheck_4526_ == 0 {
                    v_unused_4527_ = lean_ctor_get(v_fst_4487_, 2);
                    lean_dec(v_unused_4527_);
                    v___x_4505_ = v_fst_4487_;
                    v_isShared_4506_ = v_isSharedCheck_4526_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_target_4503_);
                    lean_inc(v_00_u03c3s_4502_);
                    lean_inc(v_u_4501_);
                    lean_dec(v_fst_4487_);
                    v___x_4505_ = lean_box(0);
                    v_isShared_4506_ = v_isSharedCheck_4526_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4507_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1;
                v___x_4508_ = lean_box(0);
                if v_isShared_4486_ == 0 {
                    lean_ctor_set_tag(v___x_4485_, 1);
                    lean_ctor_set(v___x_4485_, 1, v___x_4508_);
                    lean_ctor_set(v___x_4485_, 0, v_u_4469_);
                    v___x_4510_ = v___x_4485_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_u_4469_);
                    lean_ctor_set(v_reuseFailAlloc_4525_, 1, v___x_4508_);
                    v___x_4510_ = v_reuseFailAlloc_4525_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4511_ = l_Lean_mkConst(v___x_4507_, v___x_4510_);
                lean_inc_ref(v_target_4503_);
                lean_inc(v_fst_4497_);
                v___x_4512_ = l_Lean_mkApp4(
                    v___x_4511_,
                    v_00_u03c3s_4470_,
                    v_fst_4497_,
                    v_target_4503_,
                    v_snd_4488_,
                );
                if v_isShared_4506_ == 0 {
                    lean_ctor_set(v___x_4505_, 2, v_fst_4497_);
                    v___x_4514_ = v___x_4505_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4524_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_u_4501_);
                    lean_ctor_set(v_reuseFailAlloc_4524_, 1, v_00_u03c3s_4502_);
                    lean_ctor_set(v_reuseFailAlloc_4524_, 2, v_fst_4497_);
                    lean_ctor_set(v_reuseFailAlloc_4524_, 3, v_target_4503_);
                    v___x_4514_ = v_reuseFailAlloc_4524_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4500_ == 0 {
                    lean_ctor_set(v___x_4499_, 1, v___x_4512_);
                    lean_ctor_set(v___x_4499_, 0, v___x_4514_);
                    v___x_4516_ = v___x_4499_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4514_);
                    lean_ctor_set(v_reuseFailAlloc_4523_, 1, v___x_4512_);
                    v___x_4516_ = v_reuseFailAlloc_4523_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4491_ == 0 {
                    lean_ctor_set(v___x_4490_, 1, v___x_4516_);
                    lean_ctor_set(v___x_4490_, 0, v_fst_4483_);
                    v___x_4518_ = v___x_4490_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_fst_4483_);
                    lean_ctor_set(v_reuseFailAlloc_4522_, 1, v___x_4516_);
                    v___x_4518_ = v_reuseFailAlloc_4522_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4496_ == 0 {
                    lean_ctor_set(v___x_4495_, 0, v___x_4518_);
                    v___x_4520_ = v___x_4495_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4518_);
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
                    v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
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
    mut v_u_4541_: *mut LeanObject,
    mut v_00_u03c3s_4542_: *mut LeanObject,
    mut v_k_4543_: *mut LeanObject,
    mut v_x_4544_: *mut LeanObject,
    mut v___h_u03c6_4545_: *mut LeanObject,
    mut v___y_4546_: *mut LeanObject,
    mut v___y_4547_: *mut LeanObject,
    mut v___y_4548_: *mut LeanObject,
    mut v___y_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4551_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4549_);
    lean_dec_ref(v___y_4548_);
    lean_dec(v___y_4547_);
    lean_dec_ref(v___y_4546_);
    lean_dec_ref(v___h_u03c6_4545_);
    lean_dec_ref(v_x_4544_);
    return v_res_4551_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(
    mut v_u_4568_: *mut LeanObject,
    mut v_00_u03c3s_4569_: *mut LeanObject,
    mut v_k_4570_: *mut LeanObject,
    mut v_tail_4571_: *mut LeanObject,
    mut v_fst_4572_: *mut LeanObject,
    mut v_H_u2081_x27_4573_: *mut LeanObject,
    mut v___y_4574_: *mut LeanObject,
    mut v___y_4575_: *mut LeanObject,
    mut v___y_4576_: *mut LeanObject,
    mut v___y_4577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4585_: u8 = 0;
    let mut v_fst_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4590_: u8 = 0;
    let mut v_fst_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4596_: u8 = 0;
    let mut v_u_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4602_: u8 = 0;
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4622_: u8 = 0;
    let mut v_unused_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4624_: u8 = 0;
    let mut v_unused_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut v_isSharedCheck_4627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_H_u2081_x27_4573_);
                lean_inc_ref_n(v_00_u03c3s_4569_, 2);
                lean_inc_n(v_u_4568_, 2);
                v___f_4579_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    10,
                    4,
                );
                lean_closure_set(v___f_4579_, 0, v_u_4568_);
                lean_closure_set(v___f_4579_, 1, v_00_u03c3s_4569_);
                lean_closure_set(v___f_4579_, 2, v_H_u2081_x27_4573_);
                lean_closure_set(v___f_4579_, 3, v_k_4570_);
                v___x_4580_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_4580_, 0, v_tail_4571_);
                lean_inc_ref(v_fst_4572_);
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
                if lean_obj_tag(v___x_4581_) == 0 {
                    v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
                    v_isSharedCheck_4627_ = (!lean_is_exclusive(v___x_4581_)) as u8;
                    if v_isSharedCheck_4627_ == 0 {
                        v___x_4584_ = v___x_4581_;
                        v_isShared_4585_ = v_isSharedCheck_4627_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4582_);
                        lean_dec(v___x_4581_);
                        v___x_4584_ = lean_box(0);
                        v_isShared_4585_ = v_isSharedCheck_4627_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_H_u2081_x27_4573_);
                    lean_dec_ref(v_fst_4572_);
                    lean_dec_ref(v_00_u03c3s_4569_);
                    lean_dec(v_u_4568_);
                    return v___x_4581_;
                }
            }
            1 => {
                v_fst_4586_ = lean_ctor_get(v_a_4582_, 0);
                v_snd_4587_ = lean_ctor_get(v_a_4582_, 1);
                v_isSharedCheck_4626_ = (!lean_is_exclusive(v_a_4582_)) as u8;
                if v_isSharedCheck_4626_ == 0 {
                    v___x_4589_ = v_a_4582_;
                    v_isShared_4590_ = v_isSharedCheck_4626_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4587_);
                    lean_inc(v_fst_4586_);
                    lean_dec(v_a_4582_);
                    v___x_4589_ = lean_box(0);
                    v_isShared_4590_ = v_isSharedCheck_4626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_4591_ = lean_ctor_get(v_snd_4587_, 0);
                lean_inc(v_fst_4591_);
                v_snd_4592_ = lean_ctor_get(v_fst_4586_, 1);
                v_snd_4593_ = lean_ctor_get(v_snd_4587_, 1);
                v_isSharedCheck_4624_ = (!lean_is_exclusive(v_snd_4587_)) as u8;
                if v_isSharedCheck_4624_ == 0 {
                    v_unused_4625_ = lean_ctor_get(v_snd_4587_, 0);
                    lean_dec(v_unused_4625_);
                    v___x_4595_ = v_snd_4587_;
                    v_isShared_4596_ = v_isSharedCheck_4624_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_4593_);
                    lean_dec(v_snd_4587_);
                    v___x_4595_ = lean_box(0);
                    v_isShared_4596_ = v_isSharedCheck_4624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_u_4597_ = lean_ctor_get(v_fst_4591_, 0);
                v_00_u03c3s_4598_ = lean_ctor_get(v_fst_4591_, 1);
                v_target_4599_ = lean_ctor_get(v_fst_4591_, 3);
                v_isSharedCheck_4622_ = (!lean_is_exclusive(v_fst_4591_)) as u8;
                if v_isSharedCheck_4622_ == 0 {
                    v_unused_4623_ = lean_ctor_get(v_fst_4591_, 2);
                    lean_dec(v_unused_4623_);
                    v___x_4601_ = v_fst_4591_;
                    v_isShared_4602_ = v_isSharedCheck_4622_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_target_4599_);
                    lean_inc(v_00_u03c3s_4598_);
                    lean_inc(v_u_4597_);
                    lean_dec(v_fst_4591_);
                    v___x_4601_ = lean_box(0);
                    v_isShared_4602_ = v_isSharedCheck_4622_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4603_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1;
                v___x_4604_ = lean_box(0);
                lean_inc_n(v_u_4568_, 2);
                v___x_4605_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4605_, 0, v_u_4568_);
                lean_ctor_set(v___x_4605_, 1, v___x_4604_);
                v___x_4606_ = l_Lean_mkConst(v___x_4603_, v___x_4605_);
                lean_inc_ref(v_target_4599_);
                lean_inc_ref(v_fst_4572_);
                lean_inc_ref(v_H_u2081_x27_4573_);
                lean_inc_n(v_snd_4592_, 2);
                lean_inc_ref_n(v_00_u03c3s_4569_, 2);
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
                    lean_ctor_set(v___x_4601_, 2, v___x_4609_);
                    v___x_4611_ = v___x_4601_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_u_4597_);
                    lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_00_u03c3s_4598_);
                    lean_ctor_set(v_reuseFailAlloc_4621_, 2, v___x_4609_);
                    lean_ctor_set(v_reuseFailAlloc_4621_, 3, v_target_4599_);
                    v___x_4611_ = v_reuseFailAlloc_4621_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4596_ == 0 {
                    lean_ctor_set(v___x_4595_, 1, v___x_4607_);
                    lean_ctor_set(v___x_4595_, 0, v___x_4611_);
                    v___x_4613_ = v___x_4595_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4611_);
                    lean_ctor_set(v_reuseFailAlloc_4620_, 1, v___x_4607_);
                    v___x_4613_ = v_reuseFailAlloc_4620_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4590_ == 0 {
                    lean_ctor_set(v___x_4589_, 1, v___x_4613_);
                    v___x_4615_ = v___x_4589_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_fst_4586_);
                    lean_ctor_set(v_reuseFailAlloc_4619_, 1, v___x_4613_);
                    v___x_4615_ = v_reuseFailAlloc_4619_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4585_ == 0 {
                    lean_ctor_set(v___x_4584_, 0, v___x_4615_);
                    v___x_4617_ = v___x_4584_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4615_);
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
    mut v_u_4628_: *mut LeanObject,
    mut v_00_u03c3s_4629_: *mut LeanObject,
    mut v_k_4630_: *mut LeanObject,
    mut v_tail_4631_: *mut LeanObject,
    mut v_fst_4632_: *mut LeanObject,
    mut v_H_u2081_x27_4633_: *mut LeanObject,
    mut v___y_4634_: *mut LeanObject,
    mut v___y_4635_: *mut LeanObject,
    mut v___y_4636_: *mut LeanObject,
    mut v___y_4637_: *mut LeanObject,
    mut v___y_4638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4639_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4637_);
    lean_dec_ref(v___y_4636_);
    lean_dec(v___y_4635_);
    lean_dec_ref(v___y_4634_);
    return v_res_4639_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    v___x_4649_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4;
    v___x_4650_ = l_Lean_stringToMessageData(v___x_4649_);
    return v___x_4650_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed(
    mut v___x_4651_: *mut LeanObject,
    mut v_tail_4652_: *mut LeanObject,
    mut v_u_4653_: *mut LeanObject,
    mut v___x_4654_: *mut LeanObject,
    mut v_k_4655_: *mut LeanObject,
    mut v_x_4656_: *mut LeanObject,
    mut v___y_4657_: *mut LeanObject,
    mut v___y_4658_: *mut LeanObject,
    mut v___y_4659_: *mut LeanObject,
    mut v___y_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4662_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4660_);
    lean_dec_ref(v___y_4659_);
    lean_dec(v___y_4658_);
    lean_dec_ref(v___y_4657_);
    return v_res_4662_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    v___x_4664_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6;
    v___x_4665_ = l_Lean_stringToMessageData(v___x_4664_);
    return v___x_4665_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    v___x_4673_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10;
    v___x_4674_ = l_Lean_stringToMessageData(v___x_4673_);
    return v___x_4674_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(
    mut v_u_4681_: *mut LeanObject,
    mut v_00_u03c3s_4682_: *mut LeanObject,
    mut v_H_4683_: *mut LeanObject,
    mut v_pat_4684_: *mut LeanObject,
    mut v_k_4685_: *mut LeanObject,
    mut v_a_4686_: *mut LeanObject,
    mut v_a_4687_: *mut LeanObject,
    mut v_a_4688_: *mut LeanObject,
    mut v_a_4689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4694_: u8 = 0;
    let mut v___y_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4697_: u8 = 0;
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: u8 = 0;
    let mut v___x_4706_: u8 = 0;
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: u8 = 0;
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4725_: u8 = 0;
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4729_: u8 = 0;
    let mut v_a_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4733_: u8 = 0;
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut v_isSharedCheck_4738_: u8 = 0;
    let mut v_H_x27_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4746_: u8 = 0;
    let mut v_fst_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4751_: u8 = 0;
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4756_: u8 = 0;
    let mut v_fst_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4760_: u8 = 0;
    let mut v_u_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4766_: u8 = 0;
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut v_unused_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4789_: u8 = 0;
    let mut v_unused_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4791_: u8 = 0;
    let mut v_a_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4795_: u8 = 0;
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4799_: u8 = 0;
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut v_isSharedCheck_4801_: u8 = 0;
    let mut v_args_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4811_: u8 = 0;
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4824_: u8 = 0;
    let mut v_fst_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4832_: u8 = 0;
    let mut v_snd_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4836_: u8 = 0;
    let mut v_u_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4842_: u8 = 0;
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4863_: u8 = 0;
    let mut v_unused_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4865_: u8 = 0;
    let mut v_unused_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4867_: u8 = 0;
    let mut v_isSharedCheck_4868_: u8 = 0;
    let mut v_a_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4872_: u8 = 0;
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4876_: u8 = 0;
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: u8 = 0;
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4896_: u8 = 0;
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4900_: u8 = 0;
    let mut v_isSharedCheck_4901_: u8 = 0;
    let mut v_unused_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4906_: u8 = 0;
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4914_: u8 = 0;
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: u8 = 0;
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4947_: u8 = 0;
    let mut v_fst_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4951_: u8 = 0;
    let mut v_u_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4957_: u8 = 0;
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4980_: u8 = 0;
    let mut v_unused_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4982_: u8 = 0;
    let mut v_unused_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4984_: u8 = 0;
    let mut v_a_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4988_: u8 = 0;
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4992_: u8 = 0;
    let mut v_isSharedCheck_4993_: u8 = 0;
    let mut v_unused_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4996_: u8 = 0;
    let mut v_unused_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4998_: u8 = 0;
    let mut v_h_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: u8 = 0;
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5018_: u8 = 0;
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5022_: u8 = 0;
    let mut v_a_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5026_: u8 = 0;
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5030_: u8 = 0;
    let mut v_a_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5034_: u8 = 0;
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_pat_4684_) {
                0 => {
                    v_name_4691_ = lean_ctor_get(v_pat_4684_, 0);
                    v_isSharedCheck_4738_ = (!lean_is_exclusive(v_pat_4684_)) as u8;
                    if v_isSharedCheck_4738_ == 0 {
                        v___x_4693_ = v_pat_4684_;
                        v_isShared_4694_ = v_isSharedCheck_4738_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_name_4691_);
                        lean_dec(v_pat_4684_);
                        v___x_4693_ = lean_box(0);
                        v_isShared_4694_ = v_isSharedCheck_4738_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    lean_inc_ref(v_00_u03c3s_4682_);
                    lean_inc(v_u_4681_);
                    v_H_x27_4739_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_4681_, v_00_u03c3s_4682_);
                    lean_inc(v_a_4689_);
                    lean_inc_ref(v_a_4688_);
                    lean_inc(v_a_4687_);
                    lean_inc_ref(v_a_4686_);
                    v___x_4740_ = lean_apply_6(
                        v_k_4685_,
                        v_H_x27_4739_,
                        v_a_4686_,
                        v_a_4687_,
                        v_a_4688_,
                        v_a_4689_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4740_) == 0 {
                        v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
                        lean_inc(v_a_4741_);
                        lean_dec_ref_known(v___x_4740_, 1);
                        v_snd_4742_ = lean_ctor_get(v_a_4741_, 1);
                        v_fst_4743_ = lean_ctor_get(v_a_4741_, 0);
                        v_isSharedCheck_4801_ = (!lean_is_exclusive(v_a_4741_)) as u8;
                        if v_isSharedCheck_4801_ == 0 {
                            v___x_4745_ = v_a_4741_;
                            v_isShared_4746_ = v_isSharedCheck_4801_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_snd_4742_);
                            lean_inc(v_fst_4743_);
                            lean_dec(v_a_4741_);
                            v___x_4745_ = lean_box(0);
                            v_isShared_4746_ = v_isSharedCheck_4801_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_H_4683_);
                        lean_dec_ref(v_00_u03c3s_4682_);
                        lean_dec(v_u_4681_);
                        return v___x_4740_;
                    }
                }
                2 => {
                    v_args_4802_ = lean_ctor_get(v_pat_4684_, 0);
                    lean_inc(v_args_4802_);
                    lean_dec_ref_known(v_pat_4684_, 1);
                    if lean_obj_tag(v_args_4802_) == 0 {
                        v___x_4803_ = lean_box(1);
                        v_pat_4684_ = v___x_4803_;
                        state = 0;
                        continue;
                    } else {
                        v_tail_4805_ = lean_ctor_get(v_args_4802_, 1);
                        if lean_obj_tag(v_tail_4805_) == 0 {
                            v_head_4806_ = lean_ctor_get(v_args_4802_, 0);
                            lean_inc(v_head_4806_);
                            lean_dec_ref_known(v_args_4802_, 2);
                            v_pat_4684_ = v_head_4806_;
                            state = 0;
                            continue;
                        } else {
                            lean_inc(v_tail_4805_);
                            v_head_4808_ = lean_ctor_get(v_args_4802_, 0);
                            v_isSharedCheck_4901_ = (!lean_is_exclusive(v_args_4802_)) as u8;
                            if v_isSharedCheck_4901_ == 0 {
                                v_unused_4902_ = lean_ctor_get(v_args_4802_, 1);
                                lean_dec(v_unused_4902_);
                                v___x_4810_ = v_args_4802_;
                                v_isShared_4811_ = v_isSharedCheck_4901_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_head_4808_);
                                lean_dec(v_args_4802_);
                                v___x_4810_ = lean_box(0);
                                v_isShared_4811_ = v_isSharedCheck_4901_;
                                state = 21;
                                continue;
                            }
                        }
                    }
                }
                3 => {
                    v_args_4903_ = lean_ctor_get(v_pat_4684_, 0);
                    v_isSharedCheck_4998_ = (!lean_is_exclusive(v_pat_4684_)) as u8;
                    if v_isSharedCheck_4998_ == 0 {
                        v___x_4905_ = v_pat_4684_;
                        v_isShared_4906_ = v_isSharedCheck_4998_;
                        state = 35;
                        continue;
                    } else {
                        lean_inc(v_args_4903_);
                        lean_dec(v_pat_4684_);
                        v___x_4905_ = lean_box(0);
                        v_isShared_4906_ = v_isSharedCheck_4998_;
                        state = 35;
                        continue;
                    }
                }
                4 => {
                    v_h_4999_ = lean_ctor_get(v_pat_4684_, 0);
                    lean_inc(v_h_4999_);
                    lean_dec_ref_known(v_pat_4684_, 1);
                    lean_inc_ref(v_00_u03c3s_4682_);
                    v___f_5000_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed
                            as *mut core::ffi::c_void,
                        10,
                        3,
                    );
                    lean_closure_set(v___f_5000_, 0, v_u_4681_);
                    lean_closure_set(v___f_5000_, 1, v_00_u03c3s_4682_);
                    lean_closure_set(v___f_5000_, 2, v_k_4685_);
                    v___x_5001_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_4682_, v_H_4683_, v_h_4999_, v___f_5000_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
                    return v___x_5001_;
                }
                _ => {
                    lean_dec(v_u_4681_);
                    v_h_5002_ = lean_ctor_get(v_pat_4684_, 0);
                    lean_inc(v_h_5002_);
                    lean_dec_ref_known(v_pat_4684_, 1);
                    v___x_5003_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(
                        v_h_5002_, v_a_4688_, v_a_4689_,
                    );
                    if lean_obj_tag(v___x_5003_) == 0 {
                        v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
                        lean_inc(v_a_5004_);
                        lean_dec_ref_known(v___x_5003_, 1);
                        v_fst_5005_ = lean_ctor_get(v_a_5004_, 0);
                        lean_inc(v_fst_5005_);
                        v_snd_5006_ = lean_ctor_get(v_a_5004_, 1);
                        lean_inc(v_snd_5006_);
                        lean_dec(v_a_5004_);
                        v___x_5007_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v_a_4689_);
                        if lean_obj_tag(v___x_5007_) == 0 {
                            v_a_5008_ = lean_ctor_get(v___x_5007_, 0);
                            lean_inc(v_a_5008_);
                            lean_dec_ref_known(v___x_5007_, 1);
                            v___x_5009_ = l_Lean_Expr_consumeMData(v_H_4683_);
                            lean_dec_ref(v_H_4683_);
                            v___x_5010_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_5010_, 0, v_fst_5005_);
                            lean_ctor_set(v___x_5010_, 1, v_a_5008_);
                            lean_ctor_set(v___x_5010_, 2, v___x_5009_);
                            v___x_5011_ = 1;
                            lean_inc_ref(v___x_5010_);
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
                            if lean_obj_tag(v___x_5012_) == 0 {
                                lean_dec_ref_known(v___x_5012_, 1);
                                v___x_5013_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_5010_);
                                lean_inc(v_a_4689_);
                                lean_inc_ref(v_a_4688_);
                                lean_inc(v_a_4687_);
                                lean_inc_ref(v_a_4686_);
                                v___x_5014_ = lean_apply_6(
                                    v_k_4685_,
                                    v___x_5013_,
                                    v_a_4686_,
                                    v_a_4687_,
                                    v_a_4688_,
                                    v_a_4689_,
                                    lean_box(0),
                                );
                                return v___x_5014_;
                            } else {
                                lean_dec_ref_known(v___x_5010_, 3);
                                lean_dec_ref(v_k_4685_);
                                v_a_5015_ = lean_ctor_get(v___x_5012_, 0);
                                v_isSharedCheck_5022_ = (!lean_is_exclusive(v___x_5012_)) as u8;
                                if v_isSharedCheck_5022_ == 0 {
                                    v___x_5017_ = v___x_5012_;
                                    v_isShared_5018_ = v_isSharedCheck_5022_;
                                    state = 49;
                                    continue;
                                } else {
                                    lean_inc(v_a_5015_);
                                    lean_dec(v___x_5012_);
                                    v___x_5017_ = lean_box(0);
                                    v_isShared_5018_ = v_isSharedCheck_5022_;
                                    state = 49;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_snd_5006_);
                            lean_dec(v_fst_5005_);
                            lean_dec_ref(v_k_4685_);
                            lean_dec_ref(v_H_4683_);
                            lean_dec_ref(v_00_u03c3s_4682_);
                            v_a_5023_ = lean_ctor_get(v___x_5007_, 0);
                            v_isSharedCheck_5030_ = (!lean_is_exclusive(v___x_5007_)) as u8;
                            if v_isSharedCheck_5030_ == 0 {
                                v___x_5025_ = v___x_5007_;
                                v_isShared_5026_ = v_isSharedCheck_5030_;
                                state = 51;
                                continue;
                            } else {
                                lean_inc(v_a_5023_);
                                lean_dec(v___x_5007_);
                                v___x_5025_ = lean_box(0);
                                v_isShared_5026_ = v_isSharedCheck_5030_;
                                state = 51;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_k_4685_);
                        lean_dec_ref(v_H_4683_);
                        lean_dec_ref(v_00_u03c3s_4682_);
                        v_a_5031_ = lean_ctor_get(v___x_5003_, 0);
                        v_isSharedCheck_5038_ = (!lean_is_exclusive(v___x_5003_)) as u8;
                        if v_isSharedCheck_5038_ == 0 {
                            v___x_5033_ = v___x_5003_;
                            v_isShared_5034_ = v_isSharedCheck_5038_;
                            state = 53;
                            continue;
                        } else {
                            lean_inc(v_a_5031_);
                            lean_dec(v___x_5003_);
                            v___x_5033_ = lean_box(0);
                            v_isShared_5034_ = v_isSharedCheck_5038_;
                            state = 53;
                            continue;
                        }
                    }
                }
            },
            1 => {
                v___x_4707_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
                v___x_4708_ = 0;
                v___x_4709_ = lean_box(0);
                v___x_4710_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_4707_,
                    v___x_4708_,
                    v___x_4709_,
                    v_a_4686_,
                    v_a_4687_,
                    v_a_4688_,
                    v_a_4689_,
                );
                if lean_obj_tag(v___x_4710_) == 0 {
                    v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
                    lean_inc(v_a_4711_);
                    lean_dec_ref_known(v___x_4710_, 1);
                    v___x_4712_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3;
                    v___x_4713_ = lean_box(0);
                    lean_inc(v_u_4681_);
                    v___x_4714_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4714_, 0, v_u_4681_);
                    lean_ctor_set(v___x_4714_, 1, v___x_4713_);
                    v___x_4715_ = l_Lean_mkConst(v___x_4712_, v___x_4714_);
                    lean_inc_ref(v_H_4683_);
                    lean_inc_ref(v_00_u03c3s_4682_);
                    v___x_4716_ =
                        l_Lean_mkApp3(v___x_4715_, v_00_u03c3s_4682_, v_H_4683_, v_a_4711_);
                    v___x_4717_ = lean_box(0);
                    v___x_4718_ = l_Lean_Meta_synthInstance(
                        v___x_4716_,
                        v___x_4717_,
                        v_a_4686_,
                        v_a_4687_,
                        v_a_4688_,
                        v_a_4689_,
                    );
                    if lean_obj_tag(v___x_4718_) == 0 {
                        lean_dec_ref_known(v___x_4718_, 1);
                        lean_inc(v_name_4691_);
                        v___x_4719_ = lean_alloc_ctor(4, 1, (0) as u32);
                        lean_ctor_set(v___x_4719_, 0, v_name_4691_);
                        lean_inc_ref(v_k_4685_);
                        lean_inc_ref(v_H_4683_);
                        lean_inc_ref(v_00_u03c3s_4682_);
                        lean_inc(v_u_4681_);
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
                        if lean_obj_tag(v___x_4720_) == 0 {
                            lean_del_object(v___x_4693_);
                            lean_dec(v_name_4691_);
                            lean_dec_ref(v_k_4685_);
                            lean_dec_ref(v_H_4683_);
                            lean_dec_ref(v_00_u03c3s_4682_);
                            lean_dec(v_u_4681_);
                            return v___x_4720_;
                        } else {
                            v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
                            lean_inc(v_a_4721_);
                            v___y_4703_ = v___x_4720_;
                            v_a_4704_ = v_a_4721_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_4722_ = lean_ctor_get(v___x_4718_, 0);
                        v_isSharedCheck_4729_ = (!lean_is_exclusive(v___x_4718_)) as u8;
                        if v_isSharedCheck_4729_ == 0 {
                            v___x_4724_ = v___x_4718_;
                            v_isShared_4725_ = v_isSharedCheck_4729_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4722_);
                            lean_dec(v___x_4718_);
                            v___x_4724_ = lean_box(0);
                            v_isShared_4725_ = v_isSharedCheck_4729_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_4730_ = lean_ctor_get(v___x_4710_, 0);
                    v_isSharedCheck_4737_ = (!lean_is_exclusive(v___x_4710_)) as u8;
                    if v_isSharedCheck_4737_ == 0 {
                        v___x_4732_ = v___x_4710_;
                        v_isShared_4733_ = v_isSharedCheck_4737_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4730_);
                        lean_dec(v___x_4710_);
                        v___x_4732_ = lean_box(0);
                        v_isShared_4733_ = v_isSharedCheck_4737_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_4697_ == 0 {
                    lean_dec_ref(v___y_4696_);
                    if v_isShared_4694_ == 0 {
                        lean_ctor_set_tag(v___x_4693_, 5);
                        v___x_4699_ = v___x_4693_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4701_ = lean_alloc_ctor(5, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_name_4691_);
                        v___x_4699_ = v_reuseFailAlloc_4701_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4693_);
                    lean_dec(v_name_4691_);
                    lean_dec_ref(v_k_4685_);
                    lean_dec_ref(v_H_4683_);
                    lean_dec_ref(v_00_u03c3s_4682_);
                    lean_dec(v_u_4681_);
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
                    lean_dec_ref(v_a_4704_);
                    v___y_4696_ = v___y_4703_;
                    v___y_4697_ = v___x_4705_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                lean_inc(v_a_4722_);
                if v_isShared_4725_ == 0 {
                    v___x_4727_ = v___x_4724_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4728_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
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
                lean_inc(v_a_4730_);
                if v_isShared_4733_ == 0 {
                    v___x_4735_ = v___x_4732_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
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
                v_fst_4747_ = lean_ctor_get(v_snd_4742_, 0);
                v_snd_4748_ = lean_ctor_get(v_snd_4742_, 1);
                v_isSharedCheck_4800_ = (!lean_is_exclusive(v_snd_4742_)) as u8;
                if v_isSharedCheck_4800_ == 0 {
                    v___x_4750_ = v_snd_4742_;
                    v_isShared_4751_ = v_isSharedCheck_4800_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_snd_4748_);
                    lean_inc(v_fst_4747_);
                    lean_dec(v_snd_4742_);
                    v___x_4750_ = lean_box(0);
                    v_isShared_4751_ = v_isSharedCheck_4800_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                lean_inc(v_fst_4747_);
                v___x_4752_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_4747_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
                if lean_obj_tag(v___x_4752_) == 0 {
                    v_a_4753_ = lean_ctor_get(v___x_4752_, 0);
                    v_isSharedCheck_4791_ = (!lean_is_exclusive(v___x_4752_)) as u8;
                    if v_isSharedCheck_4791_ == 0 {
                        v___x_4755_ = v___x_4752_;
                        v_isShared_4756_ = v_isSharedCheck_4791_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_4753_);
                        lean_dec(v___x_4752_);
                        v___x_4755_ = lean_box(0);
                        v_isShared_4756_ = v_isSharedCheck_4791_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4750_);
                    lean_dec(v_snd_4748_);
                    lean_dec(v_fst_4747_);
                    lean_del_object(v___x_4745_);
                    lean_dec(v_fst_4743_);
                    lean_dec_ref(v_H_4683_);
                    lean_dec_ref(v_00_u03c3s_4682_);
                    lean_dec(v_u_4681_);
                    v_a_4792_ = lean_ctor_get(v___x_4752_, 0);
                    v_isSharedCheck_4799_ = (!lean_is_exclusive(v___x_4752_)) as u8;
                    if v_isSharedCheck_4799_ == 0 {
                        v___x_4794_ = v___x_4752_;
                        v_isShared_4795_ = v_isSharedCheck_4799_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_4792_);
                        lean_dec(v___x_4752_);
                        v___x_4794_ = lean_box(0);
                        v_isShared_4795_ = v_isSharedCheck_4799_;
                        state = 19;
                        continue;
                    }
                }
            }
            11 => {
                v_fst_4757_ = lean_ctor_get(v_a_4753_, 0);
                v_isSharedCheck_4789_ = (!lean_is_exclusive(v_a_4753_)) as u8;
                if v_isSharedCheck_4789_ == 0 {
                    v_unused_4790_ = lean_ctor_get(v_a_4753_, 1);
                    lean_dec(v_unused_4790_);
                    v___x_4759_ = v_a_4753_;
                    v_isShared_4760_ = v_isSharedCheck_4789_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_fst_4757_);
                    lean_dec(v_a_4753_);
                    v___x_4759_ = lean_box(0);
                    v_isShared_4760_ = v_isSharedCheck_4789_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_u_4761_ = lean_ctor_get(v_fst_4747_, 0);
                v_00_u03c3s_4762_ = lean_ctor_get(v_fst_4747_, 1);
                v_target_4763_ = lean_ctor_get(v_fst_4747_, 3);
                v_isSharedCheck_4787_ = (!lean_is_exclusive(v_fst_4747_)) as u8;
                if v_isSharedCheck_4787_ == 0 {
                    v_unused_4788_ = lean_ctor_get(v_fst_4747_, 2);
                    lean_dec(v_unused_4788_);
                    v___x_4765_ = v_fst_4747_;
                    v_isShared_4766_ = v_isSharedCheck_4787_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_target_4763_);
                    lean_inc(v_00_u03c3s_4762_);
                    lean_inc(v_u_4761_);
                    lean_dec(v_fst_4747_);
                    v___x_4765_ = lean_box(0);
                    v_isShared_4766_ = v_isSharedCheck_4787_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4767_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1;
                v___x_4768_ = lean_box(0);
                lean_inc(v_u_4681_);
                if v_isShared_4746_ == 0 {
                    lean_ctor_set_tag(v___x_4745_, 1);
                    lean_ctor_set(v___x_4745_, 1, v___x_4768_);
                    lean_ctor_set(v___x_4745_, 0, v_u_4681_);
                    v___x_4770_ = v___x_4745_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_u_4681_);
                    lean_ctor_set(v_reuseFailAlloc_4786_, 1, v___x_4768_);
                    v___x_4770_ = v_reuseFailAlloc_4786_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4771_ = l_Lean_mkConst(v___x_4767_, v___x_4770_);
                lean_inc_ref(v_target_4763_);
                lean_inc_ref(v_H_4683_);
                lean_inc(v_fst_4757_);
                lean_inc_ref(v_00_u03c3s_4682_);
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
                    lean_ctor_set(v___x_4765_, 2, v___x_4773_);
                    v___x_4775_ = v___x_4765_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_u_4761_);
                    lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_00_u03c3s_4762_);
                    lean_ctor_set(v_reuseFailAlloc_4785_, 2, v___x_4773_);
                    lean_ctor_set(v_reuseFailAlloc_4785_, 3, v_target_4763_);
                    v___x_4775_ = v_reuseFailAlloc_4785_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_4760_ == 0 {
                    lean_ctor_set(v___x_4759_, 1, v___x_4772_);
                    lean_ctor_set(v___x_4759_, 0, v___x_4775_);
                    v___x_4777_ = v___x_4759_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4784_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4775_);
                    lean_ctor_set(v_reuseFailAlloc_4784_, 1, v___x_4772_);
                    v___x_4777_ = v_reuseFailAlloc_4784_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_4751_ == 0 {
                    lean_ctor_set(v___x_4750_, 1, v___x_4777_);
                    lean_ctor_set(v___x_4750_, 0, v_fst_4743_);
                    v___x_4779_ = v___x_4750_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4783_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_fst_4743_);
                    lean_ctor_set(v_reuseFailAlloc_4783_, 1, v___x_4777_);
                    v___x_4779_ = v_reuseFailAlloc_4783_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_4756_ == 0 {
                    lean_ctor_set(v___x_4755_, 0, v___x_4779_);
                    v___x_4781_ = v___x_4755_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___x_4779_);
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
                    v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
                    v___x_4797_ = v_reuseFailAlloc_4798_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4797_;
            }
            21 => {
                lean_inc_ref(v_H_4683_);
                lean_inc_ref(v_00_u03c3s_4682_);
                lean_inc(v_u_4681_);
                v___x_4812_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(
                    v_u_4681_,
                    v_00_u03c3s_4682_,
                    v_H_4683_,
                    v_a_4686_,
                    v_a_4687_,
                    v_a_4688_,
                    v_a_4689_,
                );
                if lean_obj_tag(v___x_4812_) == 0 {
                    v_a_4813_ = lean_ctor_get(v___x_4812_, 0);
                    lean_inc(v_a_4813_);
                    lean_dec_ref_known(v___x_4812_, 1);
                    if lean_obj_tag(v_a_4813_) == 1 {
                        v_val_4814_ = lean_ctor_get(v_a_4813_, 0);
                        lean_inc(v_val_4814_);
                        lean_dec_ref_known(v_a_4813_, 1);
                        v_snd_4815_ = lean_ctor_get(v_val_4814_, 1);
                        lean_inc(v_snd_4815_);
                        v_fst_4816_ = lean_ctor_get(v_val_4814_, 0);
                        lean_inc_n(v_fst_4816_, 2);
                        lean_dec(v_val_4814_);
                        v_fst_4817_ = lean_ctor_get(v_snd_4815_, 0);
                        lean_inc_n(v_fst_4817_, 2);
                        v_snd_4818_ = lean_ctor_get(v_snd_4815_, 1);
                        lean_inc(v_snd_4818_);
                        lean_dec(v_snd_4815_);
                        lean_inc_ref_n(v_00_u03c3s_4682_, 2);
                        lean_inc_n(v_u_4681_, 2);
                        v___f_4819_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed
                                as *mut core::ffi::c_void,
                            11,
                            5,
                        );
                        lean_closure_set(v___f_4819_, 0, v_u_4681_);
                        lean_closure_set(v___f_4819_, 1, v_00_u03c3s_4682_);
                        lean_closure_set(v___f_4819_, 2, v_k_4685_);
                        lean_closure_set(v___f_4819_, 3, v_tail_4805_);
                        lean_closure_set(v___f_4819_, 4, v_fst_4817_);
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
                        if lean_obj_tag(v___x_4820_) == 0 {
                            v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
                            v_isSharedCheck_4868_ = (!lean_is_exclusive(v___x_4820_)) as u8;
                            if v_isSharedCheck_4868_ == 0 {
                                v___x_4823_ = v___x_4820_;
                                v_isShared_4824_ = v_isSharedCheck_4868_;
                                state = 22;
                                continue;
                            } else {
                                lean_inc(v_a_4821_);
                                lean_dec(v___x_4820_);
                                v___x_4823_ = lean_box(0);
                                v_isShared_4824_ = v_isSharedCheck_4868_;
                                state = 22;
                                continue;
                            }
                        } else {
                            lean_dec(v_snd_4818_);
                            lean_dec(v_fst_4817_);
                            lean_dec(v_fst_4816_);
                            lean_del_object(v___x_4810_);
                            lean_dec_ref(v_H_4683_);
                            lean_dec_ref(v_00_u03c3s_4682_);
                            lean_dec(v_u_4681_);
                            v_a_4869_ = lean_ctor_get(v___x_4820_, 0);
                            v_isSharedCheck_4876_ = (!lean_is_exclusive(v___x_4820_)) as u8;
                            if v_isSharedCheck_4876_ == 0 {
                                v___x_4871_ = v___x_4820_;
                                v_isShared_4872_ = v_isSharedCheck_4876_;
                                state = 31;
                                continue;
                            } else {
                                lean_inc(v_a_4869_);
                                lean_dec(v___x_4820_);
                                v___x_4871_ = lean_box(0);
                                v_isShared_4872_ = v_isSharedCheck_4876_;
                                state = 31;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4813_);
                        lean_del_object(v___x_4810_);
                        lean_dec_ref(v_00_u03c3s_4682_);
                        v___x_4877_ = l_Lean_Expr_consumeMData(v_H_4683_);
                        v___x_4878_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1;
                        v___x_4879_ = lean_unsigned_to_nat(3);
                        v___x_4880_ =
                            l_Lean_Expr_isAppOfArity(v___x_4877_, v___x_4878_, v___x_4879_);
                        if v___x_4880_ == 0 {
                            lean_dec_ref(v___x_4877_);
                            lean_dec(v_head_4808_);
                            lean_dec(v_tail_4805_);
                            lean_dec_ref(v_k_4685_);
                            lean_dec(v_u_4681_);
                            v___x_4881_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5);
                            v___x_4882_ = l_Lean_MessageData_ofExpr(v_H_4683_);
                            v___x_4883_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4883_, 0, v___x_4881_);
                            lean_ctor_set(v___x_4883_, 1, v___x_4882_);
                            v___x_4884_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_4883_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
                            return v___x_4884_;
                        } else {
                            if lean_obj_tag(v_head_4808_) == 0 {
                                v_name_4885_ = lean_ctor_get(v_head_4808_, 0);
                                lean_inc(v_name_4885_);
                                lean_dec_ref_known(v_head_4808_, 1);
                                v___x_4886_ = l_Lean_Expr_appFn_x21(v___x_4877_);
                                v___x_4887_ = l_Lean_Expr_appArg_x21(v___x_4886_);
                                lean_dec_ref(v___x_4886_);
                                v___x_4888_ = l_Lean_Expr_appArg_x21(v___x_4877_);
                                lean_dec_ref(v___x_4877_);
                                v___f_4889_ = lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed as *mut core::ffi::c_void, 11, 5);
                                lean_closure_set(v___f_4889_, 0, v___x_4888_);
                                lean_closure_set(v___f_4889_, 1, v_tail_4805_);
                                lean_closure_set(v___f_4889_, 2, v_u_4681_);
                                lean_closure_set(v___f_4889_, 3, v___x_4887_);
                                lean_closure_set(v___f_4889_, 4, v_k_4685_);
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
                                lean_dec_ref(v___x_4877_);
                                lean_dec(v_head_4808_);
                                lean_dec(v_tail_4805_);
                                lean_dec_ref(v_k_4685_);
                                lean_dec_ref(v_H_4683_);
                                lean_dec(v_u_4681_);
                                v___x_4891_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7);
                                v___x_4892_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_4891_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
                                return v___x_4892_;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4810_);
                    lean_dec(v_head_4808_);
                    lean_dec(v_tail_4805_);
                    lean_dec_ref(v_k_4685_);
                    lean_dec_ref(v_H_4683_);
                    lean_dec_ref(v_00_u03c3s_4682_);
                    lean_dec(v_u_4681_);
                    v_a_4893_ = lean_ctor_get(v___x_4812_, 0);
                    v_isSharedCheck_4900_ = (!lean_is_exclusive(v___x_4812_)) as u8;
                    if v_isSharedCheck_4900_ == 0 {
                        v___x_4895_ = v___x_4812_;
                        v_isShared_4896_ = v_isSharedCheck_4900_;
                        state = 33;
                        continue;
                    } else {
                        lean_inc(v_a_4893_);
                        lean_dec(v___x_4812_);
                        v___x_4895_ = lean_box(0);
                        v_isShared_4896_ = v_isSharedCheck_4900_;
                        state = 33;
                        continue;
                    }
                }
            }
            22 => {
                v_fst_4825_ = lean_ctor_get(v_a_4821_, 0);
                lean_inc(v_fst_4825_);
                v_snd_4826_ = lean_ctor_get(v_a_4821_, 1);
                lean_inc(v_snd_4826_);
                lean_dec(v_a_4821_);
                v_fst_4827_ = lean_ctor_get(v_snd_4826_, 0);
                lean_inc(v_fst_4827_);
                v_fst_4828_ = lean_ctor_get(v_fst_4825_, 0);
                v_snd_4829_ = lean_ctor_get(v_fst_4825_, 1);
                v_isSharedCheck_4867_ = (!lean_is_exclusive(v_fst_4825_)) as u8;
                if v_isSharedCheck_4867_ == 0 {
                    v___x_4831_ = v_fst_4825_;
                    v_isShared_4832_ = v_isSharedCheck_4867_;
                    state = 23;
                    continue;
                } else {
                    lean_inc(v_snd_4829_);
                    lean_inc(v_fst_4828_);
                    lean_dec(v_fst_4825_);
                    v___x_4831_ = lean_box(0);
                    v_isShared_4832_ = v_isSharedCheck_4867_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v_snd_4833_ = lean_ctor_get(v_snd_4826_, 1);
                v_isSharedCheck_4865_ = (!lean_is_exclusive(v_snd_4826_)) as u8;
                if v_isSharedCheck_4865_ == 0 {
                    v_unused_4866_ = lean_ctor_get(v_snd_4826_, 0);
                    lean_dec(v_unused_4866_);
                    v___x_4835_ = v_snd_4826_;
                    v_isShared_4836_ = v_isSharedCheck_4865_;
                    state = 24;
                    continue;
                } else {
                    lean_inc(v_snd_4833_);
                    lean_dec(v_snd_4826_);
                    v___x_4835_ = lean_box(0);
                    v_isShared_4836_ = v_isSharedCheck_4865_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v_u_4837_ = lean_ctor_get(v_fst_4827_, 0);
                v_00_u03c3s_4838_ = lean_ctor_get(v_fst_4827_, 1);
                v_target_4839_ = lean_ctor_get(v_fst_4827_, 3);
                v_isSharedCheck_4863_ = (!lean_is_exclusive(v_fst_4827_)) as u8;
                if v_isSharedCheck_4863_ == 0 {
                    v_unused_4864_ = lean_ctor_get(v_fst_4827_, 2);
                    lean_dec(v_unused_4864_);
                    v___x_4841_ = v_fst_4827_;
                    v_isShared_4842_ = v_isSharedCheck_4863_;
                    state = 25;
                    continue;
                } else {
                    lean_inc(v_target_4839_);
                    lean_inc(v_00_u03c3s_4838_);
                    lean_inc(v_u_4837_);
                    lean_dec(v_fst_4827_);
                    v___x_4841_ = lean_box(0);
                    v_isShared_4842_ = v_isSharedCheck_4863_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_4843_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3;
                v___x_4844_ = lean_box(0);
                lean_inc(v_u_4681_);
                if v_isShared_4811_ == 0 {
                    lean_ctor_set(v___x_4810_, 1, v___x_4844_);
                    lean_ctor_set(v___x_4810_, 0, v_u_4681_);
                    v___x_4846_ = v___x_4810_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_u_4681_);
                    lean_ctor_set(v_reuseFailAlloc_4862_, 1, v___x_4844_);
                    v___x_4846_ = v_reuseFailAlloc_4862_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_4847_ = l_Lean_mkConst(v___x_4843_, v___x_4846_);
                lean_inc_ref(v_target_4839_);
                lean_inc_ref(v_H_4683_);
                lean_inc(v_snd_4829_);
                lean_inc_ref(v_00_u03c3s_4682_);
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
                    lean_ctor_set(v___x_4841_, 2, v___x_4849_);
                    v___x_4851_ = v___x_4841_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_u_4837_);
                    lean_ctor_set(v_reuseFailAlloc_4861_, 1, v_00_u03c3s_4838_);
                    lean_ctor_set(v_reuseFailAlloc_4861_, 2, v___x_4849_);
                    lean_ctor_set(v_reuseFailAlloc_4861_, 3, v_target_4839_);
                    v___x_4851_ = v_reuseFailAlloc_4861_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_4836_ == 0 {
                    lean_ctor_set(v___x_4835_, 1, v___x_4848_);
                    lean_ctor_set(v___x_4835_, 0, v___x_4851_);
                    v___x_4853_ = v___x_4835_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4851_);
                    lean_ctor_set(v_reuseFailAlloc_4860_, 1, v___x_4848_);
                    v___x_4853_ = v_reuseFailAlloc_4860_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_4832_ == 0 {
                    lean_ctor_set(v___x_4831_, 1, v___x_4853_);
                    v___x_4855_ = v___x_4831_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_fst_4828_);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 1, v___x_4853_);
                    v___x_4855_ = v_reuseFailAlloc_4859_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_4824_ == 0 {
                    lean_ctor_set(v___x_4823_, 0, v___x_4855_);
                    v___x_4857_ = v___x_4823_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4855_);
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
                    v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4869_);
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
                    v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
                    v___x_4898_ = v_reuseFailAlloc_4899_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4898_;
            }
            35 => {
                if lean_obj_tag(v_args_4903_) == 0 {
                    lean_del_object(v___x_4905_);
                    lean_dec_ref(v_k_4685_);
                    lean_dec_ref(v_H_4683_);
                    lean_dec_ref(v_00_u03c3s_4682_);
                    lean_dec(v_u_4681_);
                    v___x_4907_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
                    return v___x_4907_;
                } else {
                    v_tail_4908_ = lean_ctor_get(v_args_4903_, 1);
                    if lean_obj_tag(v_tail_4908_) == 0 {
                        lean_del_object(v___x_4905_);
                        v_head_4909_ = lean_ctor_get(v_args_4903_, 0);
                        lean_inc(v_head_4909_);
                        lean_dec_ref_known(v_args_4903_, 2);
                        v_pat_4684_ = v_head_4909_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_tail_4908_);
                        lean_dec_ref(v_00_u03c3s_4682_);
                        v_head_4911_ = lean_ctor_get(v_args_4903_, 0);
                        v_isSharedCheck_4996_ = (!lean_is_exclusive(v_args_4903_)) as u8;
                        if v_isSharedCheck_4996_ == 0 {
                            v_unused_4997_ = lean_ctor_get(v_args_4903_, 1);
                            lean_dec(v_unused_4997_);
                            v___x_4913_ = v_args_4903_;
                            v_isShared_4914_ = v_isSharedCheck_4996_;
                            state = 36;
                            continue;
                        } else {
                            lean_inc(v_head_4911_);
                            lean_dec(v_args_4903_);
                            v___x_4913_ = lean_box(0);
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
                v___x_4917_ = lean_unsigned_to_nat(3);
                v___x_4918_ = l_Lean_Expr_isAppOfArity(v___x_4915_, v___x_4916_, v___x_4917_);
                if v___x_4918_ == 0 {
                    lean_dec_ref(v___x_4915_);
                    lean_del_object(v___x_4913_);
                    lean_dec(v_head_4911_);
                    lean_dec(v_tail_4908_);
                    lean_del_object(v___x_4905_);
                    lean_dec_ref(v_k_4685_);
                    lean_dec(v_u_4681_);
                    v___x_4919_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11,
                    );
                    v___x_4920_ = l_Lean_MessageData_ofExpr(v_H_4683_);
                    v___x_4921_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4921_, 0, v___x_4919_);
                    lean_ctor_set(v___x_4921_, 1, v___x_4920_);
                    v___x_4922_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_4921_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
                    return v___x_4922_;
                } else {
                    lean_dec_ref(v_H_4683_);
                    v___x_4923_ = l_Lean_Expr_appFn_x21(v___x_4915_);
                    v___x_4924_ = l_Lean_Expr_appFn_x21(v___x_4923_);
                    v___x_4925_ = l_Lean_Expr_appArg_x21(v___x_4924_);
                    lean_dec_ref(v___x_4924_);
                    v___x_4926_ = l_Lean_Expr_appArg_x21(v___x_4923_);
                    lean_dec_ref(v___x_4923_);
                    lean_inc_ref(v_k_4685_);
                    lean_inc_ref(v___x_4926_);
                    lean_inc_ref(v___x_4925_);
                    lean_inc(v_u_4681_);
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
                    if lean_obj_tag(v___x_4927_) == 0 {
                        v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
                        lean_inc(v_a_4928_);
                        lean_dec_ref_known(v___x_4927_, 1);
                        v_snd_4929_ = lean_ctor_get(v_a_4928_, 1);
                        lean_inc(v_snd_4929_);
                        lean_dec(v_a_4928_);
                        v_fst_4930_ = lean_ctor_get(v_snd_4929_, 0);
                        lean_inc(v_fst_4930_);
                        v_snd_4931_ = lean_ctor_get(v_snd_4929_, 1);
                        lean_inc(v_snd_4931_);
                        lean_dec(v_snd_4929_);
                        v___x_4932_ = l_Lean_Expr_appArg_x21(v___x_4915_);
                        lean_dec_ref(v___x_4915_);
                        if v_isShared_4906_ == 0 {
                            lean_ctor_set(v___x_4905_, 0, v_tail_4908_);
                            v___x_4934_ = v___x_4905_;
                            state = 37;
                            continue;
                        } else {
                            v_reuseFailAlloc_4995_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_tail_4908_);
                            v___x_4934_ = v_reuseFailAlloc_4995_;
                            state = 37;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_4926_);
                        lean_dec_ref(v___x_4925_);
                        lean_dec_ref(v___x_4915_);
                        lean_del_object(v___x_4913_);
                        lean_dec(v_tail_4908_);
                        lean_del_object(v___x_4905_);
                        lean_dec_ref(v_k_4685_);
                        lean_dec(v_u_4681_);
                        return v___x_4927_;
                    }
                }
            }
            37 => {
                lean_inc_ref(v___x_4932_);
                lean_inc_ref(v___x_4925_);
                lean_inc(v_u_4681_);
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
                if lean_obj_tag(v___x_4935_) == 0 {
                    v_a_4936_ = lean_ctor_get(v___x_4935_, 0);
                    lean_inc(v_a_4936_);
                    lean_dec_ref_known(v___x_4935_, 1);
                    v_snd_4937_ = lean_ctor_get(v_a_4936_, 1);
                    lean_inc(v_snd_4937_);
                    v_fst_4938_ = lean_ctor_get(v_a_4936_, 0);
                    lean_inc(v_fst_4938_);
                    lean_dec(v_a_4936_);
                    v_snd_4939_ = lean_ctor_get(v_snd_4937_, 1);
                    v_isSharedCheck_4993_ = (!lean_is_exclusive(v_snd_4937_)) as u8;
                    if v_isSharedCheck_4993_ == 0 {
                        v_unused_4994_ = lean_ctor_get(v_snd_4937_, 0);
                        lean_dec(v_unused_4994_);
                        v___x_4941_ = v_snd_4937_;
                        v_isShared_4942_ = v_isSharedCheck_4993_;
                        state = 38;
                        continue;
                    } else {
                        lean_inc(v_snd_4939_);
                        lean_dec(v_snd_4937_);
                        v___x_4941_ = lean_box(0);
                        v_isShared_4942_ = v_isSharedCheck_4993_;
                        state = 38;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_4932_);
                    lean_dec(v_snd_4931_);
                    lean_dec(v_fst_4930_);
                    lean_dec_ref(v___x_4926_);
                    lean_dec_ref(v___x_4925_);
                    lean_del_object(v___x_4913_);
                    lean_dec(v_u_4681_);
                    return v___x_4935_;
                }
            }
            38 => {
                lean_inc(v_fst_4930_);
                v___x_4943_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_4930_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
                if lean_obj_tag(v___x_4943_) == 0 {
                    v_a_4944_ = lean_ctor_get(v___x_4943_, 0);
                    v_isSharedCheck_4984_ = (!lean_is_exclusive(v___x_4943_)) as u8;
                    if v_isSharedCheck_4984_ == 0 {
                        v___x_4946_ = v___x_4943_;
                        v_isShared_4947_ = v_isSharedCheck_4984_;
                        state = 39;
                        continue;
                    } else {
                        lean_inc(v_a_4944_);
                        lean_dec(v___x_4943_);
                        v___x_4946_ = lean_box(0);
                        v_isShared_4947_ = v_isSharedCheck_4984_;
                        state = 39;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4941_);
                    lean_dec(v_snd_4939_);
                    lean_dec(v_fst_4938_);
                    lean_dec_ref(v___x_4932_);
                    lean_dec(v_snd_4931_);
                    lean_dec(v_fst_4930_);
                    lean_dec_ref(v___x_4926_);
                    lean_dec_ref(v___x_4925_);
                    lean_del_object(v___x_4913_);
                    lean_dec(v_u_4681_);
                    v_a_4985_ = lean_ctor_get(v___x_4943_, 0);
                    v_isSharedCheck_4992_ = (!lean_is_exclusive(v___x_4943_)) as u8;
                    if v_isSharedCheck_4992_ == 0 {
                        v___x_4987_ = v___x_4943_;
                        v_isShared_4988_ = v_isSharedCheck_4992_;
                        state = 47;
                        continue;
                    } else {
                        lean_inc(v_a_4985_);
                        lean_dec(v___x_4943_);
                        v___x_4987_ = lean_box(0);
                        v_isShared_4988_ = v_isSharedCheck_4992_;
                        state = 47;
                        continue;
                    }
                }
            }
            39 => {
                v_fst_4948_ = lean_ctor_get(v_a_4944_, 0);
                v_isSharedCheck_4982_ = (!lean_is_exclusive(v_a_4944_)) as u8;
                if v_isSharedCheck_4982_ == 0 {
                    v_unused_4983_ = lean_ctor_get(v_a_4944_, 1);
                    lean_dec(v_unused_4983_);
                    v___x_4950_ = v_a_4944_;
                    v_isShared_4951_ = v_isSharedCheck_4982_;
                    state = 40;
                    continue;
                } else {
                    lean_inc(v_fst_4948_);
                    lean_dec(v_a_4944_);
                    v___x_4950_ = lean_box(0);
                    v_isShared_4951_ = v_isSharedCheck_4982_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                v_u_4952_ = lean_ctor_get(v_fst_4930_, 0);
                v_00_u03c3s_4953_ = lean_ctor_get(v_fst_4930_, 1);
                v_target_4954_ = lean_ctor_get(v_fst_4930_, 3);
                v_isSharedCheck_4980_ = (!lean_is_exclusive(v_fst_4930_)) as u8;
                if v_isSharedCheck_4980_ == 0 {
                    v_unused_4981_ = lean_ctor_get(v_fst_4930_, 2);
                    lean_dec(v_unused_4981_);
                    v___x_4956_ = v_fst_4930_;
                    v_isShared_4957_ = v_isSharedCheck_4980_;
                    state = 41;
                    continue;
                } else {
                    lean_inc(v_target_4954_);
                    lean_inc(v_00_u03c3s_4953_);
                    lean_inc(v_u_4952_);
                    lean_dec(v_fst_4930_);
                    v___x_4956_ = lean_box(0);
                    v_isShared_4957_ = v_isSharedCheck_4980_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                v___x_4958_ = lean_box(0);
                lean_inc(v_u_4681_);
                if v_isShared_4914_ == 0 {
                    lean_ctor_set(v___x_4913_, 1, v___x_4958_);
                    lean_ctor_set(v___x_4913_, 0, v_u_4681_);
                    v___x_4960_ = v___x_4913_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_u_4681_);
                    lean_ctor_set(v_reuseFailAlloc_4979_, 1, v___x_4958_);
                    v___x_4960_ = v_reuseFailAlloc_4979_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                lean_inc_ref(v___x_4960_);
                v___x_4961_ = l_Lean_mkConst(v___x_4916_, v___x_4960_);
                lean_inc_ref(v___x_4932_);
                lean_inc_ref(v___x_4926_);
                lean_inc_ref_n(v___x_4925_, 2);
                v___x_4962_ = l_Lean_mkApp3(v___x_4961_, v___x_4925_, v___x_4926_, v___x_4932_);
                lean_inc(v_fst_4948_);
                v___x_4963_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_4681_,
                    v___x_4925_,
                    v_fst_4948_,
                    v___x_4962_,
                );
                lean_inc_ref(v_target_4954_);
                if v_isShared_4957_ == 0 {
                    lean_ctor_set(v___x_4956_, 2, v___x_4963_);
                    v___x_4965_ = v___x_4956_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4978_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_u_4952_);
                    lean_ctor_set(v_reuseFailAlloc_4978_, 1, v_00_u03c3s_4953_);
                    lean_ctor_set(v_reuseFailAlloc_4978_, 2, v___x_4963_);
                    lean_ctor_set(v_reuseFailAlloc_4978_, 3, v_target_4954_);
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
                    lean_ctor_set(v___x_4950_, 1, v___x_4968_);
                    lean_ctor_set(v___x_4950_, 0, v___x_4965_);
                    v___x_4970_ = v___x_4950_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4977_, 0, v___x_4965_);
                    lean_ctor_set(v_reuseFailAlloc_4977_, 1, v___x_4968_);
                    v___x_4970_ = v_reuseFailAlloc_4977_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_4942_ == 0 {
                    lean_ctor_set(v___x_4941_, 1, v___x_4970_);
                    lean_ctor_set(v___x_4941_, 0, v_fst_4938_);
                    v___x_4972_ = v___x_4941_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_4976_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_fst_4938_);
                    lean_ctor_set(v_reuseFailAlloc_4976_, 1, v___x_4970_);
                    v___x_4972_ = v_reuseFailAlloc_4976_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_4947_ == 0 {
                    lean_ctor_set(v___x_4946_, 0, v___x_4972_);
                    v___x_4974_ = v___x_4946_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4975_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4975_, 0, v___x_4972_);
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
                    v_reuseFailAlloc_4991_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4985_);
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
                    v_reuseFailAlloc_5021_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5015_);
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
                    v_reuseFailAlloc_5029_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5029_, 0, v_a_5023_);
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
                    v_reuseFailAlloc_5037_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5031_);
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
    mut v___x_5039_: *mut LeanObject,
    mut v_tail_5040_: *mut LeanObject,
    mut v_u_5041_: *mut LeanObject,
    mut v___x_5042_: *mut LeanObject,
    mut v_k_5043_: *mut LeanObject,
    mut v_x_5044_: *mut LeanObject,
    mut v___y_5045_: *mut LeanObject,
    mut v___y_5046_: *mut LeanObject,
    mut v___y_5047_: *mut LeanObject,
    mut v___y_5048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: u8 = 0;
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    v___x_5050_ = lean_unsigned_to_nat(1);
    v___x_5051_ = lean_mk_empty_array_with_capacity(v___x_5050_);
    v___x_5052_ = lean_array_push(v___x_5051_, v_x_5044_);
    v___x_5053_ = 0;
    v___x_5054_ = l_Lean_Expr_betaRev(v___x_5039_, v___x_5052_, v___x_5053_, v___x_5053_);
    lean_dec_ref(v___x_5052_);
    v___x_5055_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_5055_, 0, v_tail_5040_);
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
    mut v_u_5057_: *mut LeanObject,
    mut v_00_u03c3s_5058_: *mut LeanObject,
    mut v_H_5059_: *mut LeanObject,
    mut v_pat_5060_: *mut LeanObject,
    mut v_k_5061_: *mut LeanObject,
    mut v_a_5062_: *mut LeanObject,
    mut v_a_5063_: *mut LeanObject,
    mut v_a_5064_: *mut LeanObject,
    mut v_a_5065_: *mut LeanObject,
    mut v_a_5066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5067_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5065_);
    lean_dec_ref(v_a_5064_);
    lean_dec(v_a_5063_);
    lean_dec_ref(v_a_5062_);
    return v_res_5067_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(
    mut v_00_u03b1_5068_: *mut LeanObject,
    mut v_u_5069_: *mut LeanObject,
    mut v_00_u03c3s_5070_: *mut LeanObject,
    mut v_H_5071_: *mut LeanObject,
    mut v_pat_5072_: *mut LeanObject,
    mut v_k_5073_: *mut LeanObject,
    mut v_a_5074_: *mut LeanObject,
    mut v_a_5075_: *mut LeanObject,
    mut v_a_5076_: *mut LeanObject,
    mut v_a_5077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5080_: *mut LeanObject,
    mut v_u_5081_: *mut LeanObject,
    mut v_00_u03c3s_5082_: *mut LeanObject,
    mut v_H_5083_: *mut LeanObject,
    mut v_pat_5084_: *mut LeanObject,
    mut v_k_5085_: *mut LeanObject,
    mut v_a_5086_: *mut LeanObject,
    mut v_a_5087_: *mut LeanObject,
    mut v_a_5088_: *mut LeanObject,
    mut v_a_5089_: *mut LeanObject,
    mut v_a_5090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5091_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5089_);
    lean_dec_ref(v_a_5088_);
    lean_dec(v_a_5087_);
    lean_dec_ref(v_a_5086_);
    return v_res_5091_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(
    mut v_00_u03b1_5092_: *mut LeanObject,
    mut v_00_u03c3s_5093_: *mut LeanObject,
    mut v_hyp_5094_: *mut LeanObject,
    mut v_name_5095_: *mut LeanObject,
    mut v_k_5096_: *mut LeanObject,
    mut v___y_5097_: *mut LeanObject,
    mut v___y_5098_: *mut LeanObject,
    mut v___y_5099_: *mut LeanObject,
    mut v___y_5100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    v___x_5102_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_5093_, v_hyp_5094_, v_name_5095_, v_k_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
    return v___x_5102_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___boxed(
    mut v_00_u03b1_5103_: *mut LeanObject,
    mut v_00_u03c3s_5104_: *mut LeanObject,
    mut v_hyp_5105_: *mut LeanObject,
    mut v_name_5106_: *mut LeanObject,
    mut v_k_5107_: *mut LeanObject,
    mut v___y_5108_: *mut LeanObject,
    mut v___y_5109_: *mut LeanObject,
    mut v___y_5110_: *mut LeanObject,
    mut v___y_5111_: *mut LeanObject,
    mut v___y_5112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5113_: *mut LeanObject = core::ptr::null_mut();
    v_res_5113_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(v_00_u03b1_5103_, v_00_u03c3s_5104_, v_hyp_5105_, v_name_5106_, v_k_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_);
    lean_dec(v___y_5111_);
    lean_dec_ref(v___y_5110_);
    lean_dec(v___y_5109_);
    lean_dec_ref(v___y_5108_);
    return v_res_5113_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    v___x_5115_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
    v___x_5116_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5116_, 0, v___x_5115_);
    return v___x_5116_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg___boxed(
    mut v___y_5117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5118_: *mut LeanObject = core::ptr::null_mut();
    v_res_5118_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
    return v_res_5118_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(
    mut v_00_u03b1_5119_: *mut LeanObject,
    mut v___y_5120_: *mut LeanObject,
    mut v___y_5121_: *mut LeanObject,
    mut v___y_5122_: *mut LeanObject,
    mut v___y_5123_: *mut LeanObject,
    mut v___y_5124_: *mut LeanObject,
    mut v___y_5125_: *mut LeanObject,
    mut v___y_5126_: *mut LeanObject,
    mut v___y_5127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    v___x_5129_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
    return v___x_5129_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___boxed(
    mut v_00_u03b1_5130_: *mut LeanObject,
    mut v___y_5131_: *mut LeanObject,
    mut v___y_5132_: *mut LeanObject,
    mut v___y_5133_: *mut LeanObject,
    mut v___y_5134_: *mut LeanObject,
    mut v___y_5135_: *mut LeanObject,
    mut v___y_5136_: *mut LeanObject,
    mut v___y_5137_: *mut LeanObject,
    mut v___y_5138_: *mut LeanObject,
    mut v___y_5139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5140_: *mut LeanObject = core::ptr::null_mut();
    v_res_5140_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(v_00_u03b1_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
    lean_dec(v___y_5138_);
    lean_dec_ref(v___y_5137_);
    lean_dec(v___y_5136_);
    lean_dec_ref(v___y_5135_);
    lean_dec(v___y_5134_);
    lean_dec_ref(v___y_5133_);
    lean_dec(v___y_5132_);
    lean_dec_ref(v___y_5131_);
    return v_res_5140_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(
    mut v_x_5141_: *mut LeanObject,
    mut v___y_5142_: *mut LeanObject,
    mut v___y_5143_: *mut LeanObject,
    mut v___y_5144_: *mut LeanObject,
    mut v___y_5145_: *mut LeanObject,
    mut v___y_5146_: *mut LeanObject,
    mut v___y_5147_: *mut LeanObject,
    mut v___y_5148_: *mut LeanObject,
    mut v___y_5149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5145_);
    lean_inc_ref(v___y_5144_);
    lean_inc(v___y_5143_);
    lean_inc_ref(v___y_5142_);
    v___x_5151_ = lean_apply_9(
        v_x_5141_,
        v___y_5142_,
        v___y_5143_,
        v___y_5144_,
        v___y_5145_,
        v___y_5146_,
        v___y_5147_,
        v___y_5148_,
        v___y_5149_,
        lean_box(0),
    );
    return v___x_5151_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed(
    mut v_x_5152_: *mut LeanObject,
    mut v___y_5153_: *mut LeanObject,
    mut v___y_5154_: *mut LeanObject,
    mut v___y_5155_: *mut LeanObject,
    mut v___y_5156_: *mut LeanObject,
    mut v___y_5157_: *mut LeanObject,
    mut v___y_5158_: *mut LeanObject,
    mut v___y_5159_: *mut LeanObject,
    mut v___y_5160_: *mut LeanObject,
    mut v___y_5161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5162_: *mut LeanObject = core::ptr::null_mut();
    v_res_5162_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(v_x_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
    lean_dec(v___y_5156_);
    lean_dec_ref(v___y_5155_);
    lean_dec(v___y_5154_);
    lean_dec_ref(v___y_5153_);
    return v_res_5162_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(
    mut v_mvarId_5163_: *mut LeanObject,
    mut v_x_5164_: *mut LeanObject,
    mut v___y_5165_: *mut LeanObject,
    mut v___y_5166_: *mut LeanObject,
    mut v___y_5167_: *mut LeanObject,
    mut v___y_5168_: *mut LeanObject,
    mut v___y_5169_: *mut LeanObject,
    mut v___y_5170_: *mut LeanObject,
    mut v___y_5171_: *mut LeanObject,
    mut v___y_5172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5179_: u8 = 0;
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5168_);
                lean_inc_ref(v___y_5167_);
                lean_inc(v___y_5166_);
                lean_inc_ref(v___y_5165_);
                v___f_5174_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_5174_, 0, v_x_5164_);
                lean_closure_set(v___f_5174_, 1, v___y_5165_);
                lean_closure_set(v___f_5174_, 2, v___y_5166_);
                lean_closure_set(v___f_5174_, 3, v___y_5167_);
                lean_closure_set(v___f_5174_, 4, v___y_5168_);
                v___x_5175_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_5163_,
                    v___f_5174_,
                    v___y_5169_,
                    v___y_5170_,
                    v___y_5171_,
                    v___y_5172_,
                );
                if lean_obj_tag(v___x_5175_) == 0 {
                    return v___x_5175_;
                } else {
                    v_a_5176_ = lean_ctor_get(v___x_5175_, 0);
                    v_isSharedCheck_5183_ = (!lean_is_exclusive(v___x_5175_)) as u8;
                    if v_isSharedCheck_5183_ == 0 {
                        v___x_5178_ = v___x_5175_;
                        v_isShared_5179_ = v_isSharedCheck_5183_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5176_);
                        lean_dec(v___x_5175_);
                        v___x_5178_ = lean_box(0);
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
                    v_reuseFailAlloc_5182_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
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
    mut v_mvarId_5184_: *mut LeanObject,
    mut v_x_5185_: *mut LeanObject,
    mut v___y_5186_: *mut LeanObject,
    mut v___y_5187_: *mut LeanObject,
    mut v___y_5188_: *mut LeanObject,
    mut v___y_5189_: *mut LeanObject,
    mut v___y_5190_: *mut LeanObject,
    mut v___y_5191_: *mut LeanObject,
    mut v___y_5192_: *mut LeanObject,
    mut v___y_5193_: *mut LeanObject,
    mut v___y_5194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5195_: *mut LeanObject = core::ptr::null_mut();
    v_res_5195_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_5184_, v_x_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_);
    lean_dec(v___y_5193_);
    lean_dec_ref(v___y_5192_);
    lean_dec(v___y_5191_);
    lean_dec_ref(v___y_5190_);
    lean_dec(v___y_5189_);
    lean_dec_ref(v___y_5188_);
    lean_dec(v___y_5187_);
    lean_dec_ref(v___y_5186_);
    return v_res_5195_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(
    mut v_00_u03b1_5196_: *mut LeanObject,
    mut v_mvarId_5197_: *mut LeanObject,
    mut v_x_5198_: *mut LeanObject,
    mut v___y_5199_: *mut LeanObject,
    mut v___y_5200_: *mut LeanObject,
    mut v___y_5201_: *mut LeanObject,
    mut v___y_5202_: *mut LeanObject,
    mut v___y_5203_: *mut LeanObject,
    mut v___y_5204_: *mut LeanObject,
    mut v___y_5205_: *mut LeanObject,
    mut v___y_5206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    v___x_5208_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_5197_, v_x_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_);
    return v___x_5208_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___boxed(
    mut v_00_u03b1_5209_: *mut LeanObject,
    mut v_mvarId_5210_: *mut LeanObject,
    mut v_x_5211_: *mut LeanObject,
    mut v___y_5212_: *mut LeanObject,
    mut v___y_5213_: *mut LeanObject,
    mut v___y_5214_: *mut LeanObject,
    mut v___y_5215_: *mut LeanObject,
    mut v___y_5216_: *mut LeanObject,
    mut v___y_5217_: *mut LeanObject,
    mut v___y_5218_: *mut LeanObject,
    mut v___y_5219_: *mut LeanObject,
    mut v___y_5220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5221_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5219_);
    lean_dec_ref(v___y_5218_);
    lean_dec(v___y_5217_);
    lean_dec_ref(v___y_5216_);
    lean_dec(v___y_5215_);
    lean_dec_ref(v___y_5214_);
    lean_dec(v___y_5213_);
    lean_dec_ref(v___y_5212_);
    return v_res_5221_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(
    mut v_x_5222_: *mut LeanObject,
    mut v_x_5223_: *mut LeanObject,
    mut v_x_5224_: *mut LeanObject,
    mut v_x_5225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5230_: u8 = 0;
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: u8 = 0;
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: u8 = 0;
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5251_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5226_ = lean_ctor_get(v_x_5222_, 0);
                v_vs_5227_ = lean_ctor_get(v_x_5222_, 1);
                v_isSharedCheck_5251_ = (!lean_is_exclusive(v_x_5222_)) as u8;
                if v_isSharedCheck_5251_ == 0 {
                    v___x_5229_ = v_x_5222_;
                    v_isShared_5230_ = v_isSharedCheck_5251_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_5227_);
                    lean_inc(v_ks_5226_);
                    lean_dec(v_x_5222_);
                    v___x_5229_ = lean_box(0);
                    v_isShared_5230_ = v_isSharedCheck_5251_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5231_ = lean_array_get_size(v_ks_5226_);
                v___x_5232_ = lean_nat_dec_lt(v_x_5223_, v___x_5231_);
                if v___x_5232_ == 0 {
                    lean_dec(v_x_5223_);
                    v___x_5233_ = lean_array_push(v_ks_5226_, v_x_5224_);
                    v___x_5234_ = lean_array_push(v_vs_5227_, v_x_5225_);
                    if v_isShared_5230_ == 0 {
                        lean_ctor_set(v___x_5229_, 1, v___x_5234_);
                        lean_ctor_set(v___x_5229_, 0, v___x_5233_);
                        v___x_5236_ = v___x_5229_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5237_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5233_);
                        lean_ctor_set(v_reuseFailAlloc_5237_, 1, v___x_5234_);
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
                            v_reuseFailAlloc_5245_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_ks_5226_);
                            lean_ctor_set(v_reuseFailAlloc_5245_, 1, v_vs_5227_);
                            v___x_5241_ = v_reuseFailAlloc_5245_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5246_ = lean_array_fset(v_ks_5226_, v_x_5223_, v_x_5224_);
                        v___x_5247_ = lean_array_fset(v_vs_5227_, v_x_5223_, v_x_5225_);
                        lean_dec(v_x_5223_);
                        if v_isShared_5230_ == 0 {
                            lean_ctor_set(v___x_5229_, 1, v___x_5247_);
                            lean_ctor_set(v___x_5229_, 0, v___x_5246_);
                            v___x_5249_ = v___x_5229_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5250_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5250_, 0, v___x_5246_);
                            lean_ctor_set(v_reuseFailAlloc_5250_, 1, v___x_5247_);
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
                v___x_5242_ = lean_unsigned_to_nat(1);
                v___x_5243_ = lean_nat_add(v_x_5223_, v___x_5242_);
                lean_dec(v_x_5223_);
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
    mut v_n_5252_: *mut LeanObject,
    mut v_k_5253_: *mut LeanObject,
    mut v_v_5254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    v___x_5255_ = lean_unsigned_to_nat(0);
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
    v___x_5261_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0);
    v___x_5262_ = lean_usize_sub(v___x_5261_, v___x_5260_);
    return v___x_5262_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    v___x_5263_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_5263_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(
    mut v_x_5264_: *mut LeanObject,
    mut v_x_5265_: usize,
    mut v_x_5266_: usize,
    mut v_x_5267_: *mut LeanObject,
    mut v_x_5268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: usize = 0;
    let mut v___x_5271_: usize = 0;
    let mut v___x_5272_: usize = 0;
    let mut v___x_5273_: usize = 0;
    let mut v_j_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: u8 = 0;
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5279_: u8 = 0;
    let mut v_v_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5293_: u8 = 0;
    let mut v___x_5294_: u8 = 0;
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5300_: u8 = 0;
    let mut v_node_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5304_: u8 = 0;
    let mut v___x_5305_: usize = 0;
    let mut v___x_5306_: usize = 0;
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5311_: u8 = 0;
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5313_: u8 = 0;
    let mut v_unused_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5319_: u8 = 0;
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5324_: u8 = 0;
    let mut v_ks_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: usize = 0;
    let mut v___x_5331_: u8 = 0;
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: u8 = 0;
    let mut v_reuseFailAlloc_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5264_) == 0 {
                    v_es_5269_ = lean_ctor_get(v_x_5264_, 0);
                    v___x_5270_ = 5usize;
                    v___x_5271_ = 1usize;
                    v___x_5272_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1);
                    v___x_5273_ = lean_usize_land(v_x_5265_, v___x_5272_);
                    v_j_5274_ = lean_usize_to_nat(v___x_5273_);
                    v___x_5275_ = lean_array_get_size(v_es_5269_);
                    v___x_5276_ = lean_nat_dec_lt(v_j_5274_, v___x_5275_);
                    if v___x_5276_ == 0 {
                        lean_dec(v_j_5274_);
                        lean_dec(v_x_5268_);
                        lean_dec(v_x_5267_);
                        return v_x_5264_;
                    } else {
                        lean_inc_ref(v_es_5269_);
                        v_isSharedCheck_5313_ = (!lean_is_exclusive(v_x_5264_)) as u8;
                        if v_isSharedCheck_5313_ == 0 {
                            v_unused_5314_ = lean_ctor_get(v_x_5264_, 0);
                            lean_dec(v_unused_5314_);
                            v___x_5278_ = v_x_5264_;
                            v_isShared_5279_ = v_isSharedCheck_5313_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_5264_);
                            v___x_5278_ = lean_box(0);
                            v_isShared_5279_ = v_isSharedCheck_5313_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5315_ = lean_ctor_get(v_x_5264_, 0);
                    v_vs_5316_ = lean_ctor_get(v_x_5264_, 1);
                    v_isSharedCheck_5336_ = (!lean_is_exclusive(v_x_5264_)) as u8;
                    if v_isSharedCheck_5336_ == 0 {
                        v___x_5318_ = v_x_5264_;
                        v_isShared_5319_ = v_isSharedCheck_5336_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_5316_);
                        lean_inc(v_ks_5315_);
                        lean_dec(v_x_5264_);
                        v___x_5318_ = lean_box(0);
                        v_isShared_5319_ = v_isSharedCheck_5336_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5280_ = lean_array_fget(v_es_5269_, v_j_5274_);
                v___x_5281_ = lean_box(0);
                v_xs_x27_5282_ = lean_array_fset(v_es_5269_, v_j_5274_, v___x_5281_);
                match lean_obj_tag(v_v_5280_) {
                    0 => {
                        v_key_5289_ = lean_ctor_get(v_v_5280_, 0);
                        v_val_5290_ = lean_ctor_get(v_v_5280_, 1);
                        v_isSharedCheck_5300_ = (!lean_is_exclusive(v_v_5280_)) as u8;
                        if v_isSharedCheck_5300_ == 0 {
                            v___x_5292_ = v_v_5280_;
                            v_isShared_5293_ = v_isSharedCheck_5300_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_5290_);
                            lean_inc(v_key_5289_);
                            lean_dec(v_v_5280_);
                            v___x_5292_ = lean_box(0);
                            v_isShared_5293_ = v_isSharedCheck_5300_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5301_ = lean_ctor_get(v_v_5280_, 0);
                        v_isSharedCheck_5311_ = (!lean_is_exclusive(v_v_5280_)) as u8;
                        if v_isSharedCheck_5311_ == 0 {
                            v___x_5303_ = v_v_5280_;
                            v_isShared_5304_ = v_isSharedCheck_5311_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_5301_);
                            lean_dec(v_v_5280_);
                            v___x_5303_ = lean_box(0);
                            v_isShared_5304_ = v_isSharedCheck_5311_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5312_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5312_, 0, v_x_5267_);
                        lean_ctor_set(v___x_5312_, 1, v_x_5268_);
                        v___y_5284_ = v___x_5312_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5285_ = lean_array_fset(v_xs_x27_5282_, v_j_5274_, v___y_5284_);
                lean_dec(v_j_5274_);
                if v_isShared_5279_ == 0 {
                    lean_ctor_set(v___x_5278_, 0, v___x_5285_);
                    v___x_5287_ = v___x_5278_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5288_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5288_, 0, v___x_5285_);
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
                    lean_del_object(v___x_5292_);
                    v___x_5295_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5289_,
                        v_val_5290_,
                        v_x_5267_,
                        v_x_5268_,
                    );
                    v___x_5296_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5296_, 0, v___x_5295_);
                    v___y_5284_ = v___x_5296_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_5290_);
                    lean_dec(v_key_5289_);
                    if v_isShared_5293_ == 0 {
                        lean_ctor_set(v___x_5292_, 1, v_x_5268_);
                        lean_ctor_set(v___x_5292_, 0, v_x_5267_);
                        v___x_5298_ = v___x_5292_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5299_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_x_5267_);
                        lean_ctor_set(v_reuseFailAlloc_5299_, 1, v_x_5268_);
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
                    lean_ctor_set(v___x_5303_, 0, v___x_5307_);
                    v___x_5309_ = v___x_5303_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5310_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5310_, 0, v___x_5307_);
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
                    v_reuseFailAlloc_5335_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_ks_5315_);
                    lean_ctor_set(v_reuseFailAlloc_5335_, 1, v_vs_5316_);
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
                    v___x_5333_ = lean_unsigned_to_nat(4);
                    v___x_5334_ = lean_nat_dec_lt(v___x_5332_, v___x_5333_);
                    lean_dec(v___x_5332_);
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
                    v_ks_5325_ = lean_ctor_get(v_newNode_5322_, 0);
                    lean_inc_ref(v_ks_5325_);
                    v_vs_5326_ = lean_ctor_get(v_newNode_5322_, 1);
                    lean_inc_ref(v_vs_5326_);
                    lean_dec_ref(v_newNode_5322_);
                    v___x_5327_ = lean_unsigned_to_nat(0);
                    v___x_5328_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2);
                    v___x_5329_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_x_5266_, v_ks_5325_, v_vs_5326_, v___x_5327_, v___x_5328_);
                    lean_dec_ref(v_vs_5326_);
                    lean_dec_ref(v_ks_5325_);
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
    mut v_keys_5338_: *mut LeanObject,
    mut v_vals_5339_: *mut LeanObject,
    mut v_i_5340_: *mut LeanObject,
    mut v_entries_5341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: u8 = 0;
    let mut v_k_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: u64 = 0;
    let mut v_h_5347_: usize = 0;
    let mut v___x_5348_: usize = 0;
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: usize = 0;
    let mut v___x_5351_: usize = 0;
    let mut v___x_5352_: usize = 0;
    let mut v_h_5353_: usize = 0;
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5342_ = lean_array_get_size(v_keys_5338_);
                v___x_5343_ = lean_nat_dec_lt(v_i_5340_, v___x_5342_);
                if v___x_5343_ == 0 {
                    lean_dec(v_i_5340_);
                    return v_entries_5341_;
                } else {
                    v_k_5344_ = lean_array_fget_borrowed(v_keys_5338_, v_i_5340_);
                    v_v_5345_ = lean_array_fget_borrowed(v_vals_5339_, v_i_5340_);
                    v___x_5346_ = l_Lean_instHashableMVarId_hash(v_k_5344_);
                    v_h_5347_ = lean_uint64_to_usize(v___x_5346_);
                    v___x_5348_ = 5usize;
                    v___x_5349_ = lean_unsigned_to_nat(1);
                    v___x_5350_ = 1usize;
                    v___x_5351_ = lean_usize_sub(v_depth_5337_, v___x_5350_);
                    v___x_5352_ = lean_usize_mul(v___x_5348_, v___x_5351_);
                    v_h_5353_ = lean_usize_shift_right(v_h_5347_, v___x_5352_);
                    v___x_5354_ = lean_nat_add(v_i_5340_, v___x_5349_);
                    lean_dec(v_i_5340_);
                    lean_inc(v_v_5345_);
                    lean_inc(v_k_5344_);
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
    mut v_depth_5357_: *mut LeanObject,
    mut v_keys_5358_: *mut LeanObject,
    mut v_vals_5359_: *mut LeanObject,
    mut v_i_5360_: *mut LeanObject,
    mut v_entries_5361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5362_: usize = 0;
    let mut v_res_5363_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5362_ = lean_unbox_usize(v_depth_5357_);
    lean_dec(v_depth_5357_);
    v_res_5363_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_boxed_5362_, v_keys_5358_, v_vals_5359_, v_i_5360_, v_entries_5361_);
    lean_dec_ref(v_vals_5359_);
    lean_dec_ref(v_keys_5358_);
    return v_res_5363_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___boxed(
    mut v_x_5364_: *mut LeanObject,
    mut v_x_5365_: *mut LeanObject,
    mut v_x_5366_: *mut LeanObject,
    mut v_x_5367_: *mut LeanObject,
    mut v_x_5368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_20585__boxed_5369_: usize = 0;
    let mut v_x_20586__boxed_5370_: usize = 0;
    let mut v_res_5371_: *mut LeanObject = core::ptr::null_mut();
    v_x_20585__boxed_5369_ = lean_unbox_usize(v_x_5365_);
    lean_dec(v_x_5365_);
    v_x_20586__boxed_5370_ = lean_unbox_usize(v_x_5366_);
    lean_dec(v_x_5366_);
    v_res_5371_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_5364_, v_x_20585__boxed_5369_, v_x_20586__boxed_5370_, v_x_5367_, v_x_5368_);
    return v_res_5371_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(
    mut v_x_5372_: *mut LeanObject,
    mut v_x_5373_: *mut LeanObject,
    mut v_x_5374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5375_: u64 = 0;
    let mut v___x_5376_: usize = 0;
    let mut v___x_5377_: usize = 0;
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    v___x_5375_ = l_Lean_instHashableMVarId_hash(v_x_5373_);
    v___x_5376_ = lean_uint64_to_usize(v___x_5375_);
    v___x_5377_ = 1usize;
    v___x_5378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_5372_, v___x_5376_, v___x_5377_, v_x_5373_, v_x_5374_);
    return v___x_5378_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(
    mut v_mvarId_5379_: *mut LeanObject,
    mut v_val_5380_: *mut LeanObject,
    mut v___y_5381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5391_: u8 = 0;
    let mut v_depth_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5415_: u8 = 0;
    let mut v_isSharedCheck_5416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5383_ = lean_st_ref_take(v___y_5381_);
                v_mctx_5384_ = lean_ctor_get(v___x_5383_, 0);
                v_cache_5385_ = lean_ctor_get(v___x_5383_, 1);
                v_zetaDeltaFVarIds_5386_ = lean_ctor_get(v___x_5383_, 2);
                v_postponed_5387_ = lean_ctor_get(v___x_5383_, 3);
                v_diag_5388_ = lean_ctor_get(v___x_5383_, 4);
                v_isSharedCheck_5416_ = (!lean_is_exclusive(v___x_5383_)) as u8;
                if v_isSharedCheck_5416_ == 0 {
                    v___x_5390_ = v___x_5383_;
                    v_isShared_5391_ = v_isSharedCheck_5416_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_5388_);
                    lean_inc(v_postponed_5387_);
                    lean_inc(v_zetaDeltaFVarIds_5386_);
                    lean_inc(v_cache_5385_);
                    lean_inc(v_mctx_5384_);
                    lean_dec(v___x_5383_);
                    v___x_5390_ = lean_box(0);
                    v_isShared_5391_ = v_isSharedCheck_5416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_5392_ = lean_ctor_get(v_mctx_5384_, 0);
                v_levelAssignDepth_5393_ = lean_ctor_get(v_mctx_5384_, 1);
                v_lmvarCounter_5394_ = lean_ctor_get(v_mctx_5384_, 2);
                v_mvarCounter_5395_ = lean_ctor_get(v_mctx_5384_, 3);
                v_lDecls_5396_ = lean_ctor_get(v_mctx_5384_, 4);
                v_decls_5397_ = lean_ctor_get(v_mctx_5384_, 5);
                v_userNames_5398_ = lean_ctor_get(v_mctx_5384_, 6);
                v_lAssignment_5399_ = lean_ctor_get(v_mctx_5384_, 7);
                v_eAssignment_5400_ = lean_ctor_get(v_mctx_5384_, 8);
                v_dAssignment_5401_ = lean_ctor_get(v_mctx_5384_, 9);
                v_isSharedCheck_5415_ = (!lean_is_exclusive(v_mctx_5384_)) as u8;
                if v_isSharedCheck_5415_ == 0 {
                    v___x_5403_ = v_mctx_5384_;
                    v_isShared_5404_ = v_isSharedCheck_5415_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_5401_);
                    lean_inc(v_eAssignment_5400_);
                    lean_inc(v_lAssignment_5399_);
                    lean_inc(v_userNames_5398_);
                    lean_inc(v_decls_5397_);
                    lean_inc(v_lDecls_5396_);
                    lean_inc(v_mvarCounter_5395_);
                    lean_inc(v_lmvarCounter_5394_);
                    lean_inc(v_levelAssignDepth_5393_);
                    lean_inc(v_depth_5392_);
                    lean_dec(v_mctx_5384_);
                    v___x_5403_ = lean_box(0);
                    v_isShared_5404_ = v_isSharedCheck_5415_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5405_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_eAssignment_5400_, v_mvarId_5379_, v_val_5380_);
                if v_isShared_5404_ == 0 {
                    lean_ctor_set(v___x_5403_, 8, v___x_5405_);
                    v___x_5407_ = v___x_5403_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_depth_5392_);
                    lean_ctor_set(v_reuseFailAlloc_5414_, 1, v_levelAssignDepth_5393_);
                    lean_ctor_set(v_reuseFailAlloc_5414_, 2, v_lmvarCounter_5394_);
                    lean_ctor_set(v_reuseFailAlloc_5414_, 3, v_mvarCounter_5395_);
                    lean_ctor_set(v_reuseFailAlloc_5414_, 4, v_lDecls_5396_);
                    lean_ctor_set(v_reuseFailAlloc_5414_, 5, v_decls_5397_);
                    lean_ctor_set(v_reuseFailAlloc_5414_, 6, v_userNames_5398_);
                    lean_ctor_set(v_reuseFailAlloc_5414_, 7, v_lAssignment_5399_);
                    lean_ctor_set(v_reuseFailAlloc_5414_, 8, v___x_5405_);
                    lean_ctor_set(v_reuseFailAlloc_5414_, 9, v_dAssignment_5401_);
                    v___x_5407_ = v_reuseFailAlloc_5414_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5391_ == 0 {
                    lean_ctor_set(v___x_5390_, 0, v___x_5407_);
                    v___x_5409_ = v___x_5390_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5413_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5413_, 0, v___x_5407_);
                    lean_ctor_set(v_reuseFailAlloc_5413_, 1, v_cache_5385_);
                    lean_ctor_set(v_reuseFailAlloc_5413_, 2, v_zetaDeltaFVarIds_5386_);
                    lean_ctor_set(v_reuseFailAlloc_5413_, 3, v_postponed_5387_);
                    lean_ctor_set(v_reuseFailAlloc_5413_, 4, v_diag_5388_);
                    v___x_5409_ = v_reuseFailAlloc_5413_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5410_ = lean_st_ref_set(v___y_5381_, v___x_5409_);
                v___x_5411_ = lean_box(0);
                v___x_5412_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5412_, 0, v___x_5411_);
                return v___x_5412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg___boxed(
    mut v_mvarId_5417_: *mut LeanObject,
    mut v_val_5418_: *mut LeanObject,
    mut v___y_5419_: *mut LeanObject,
    mut v___y_5420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5421_: *mut LeanObject = core::ptr::null_mut();
    v_res_5421_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(
            v_mvarId_5417_,
            v_val_5418_,
            v___y_5419_,
        );
    lean_dec(v___y_5419_);
    return v_res_5421_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(
    mut v_snd_5424_: *mut LeanObject,
    mut v_hyp_5425_: *mut LeanObject,
    mut v_a_5426_: *mut LeanObject,
    mut v_fst_5427_: *mut LeanObject,
    mut v___y_5428_: *mut LeanObject,
    mut v___y_5429_: *mut LeanObject,
    mut v___y_5430_: *mut LeanObject,
    mut v___y_5431_: *mut LeanObject,
    mut v___y_5432_: *mut LeanObject,
    mut v___y_5433_: *mut LeanObject,
    mut v___y_5434_: *mut LeanObject,
    mut v___y_5435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restHyps_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5459_: u8 = 0;
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5463_: u8 = 0;
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
                lean_inc_ref(v_snd_5424_);
                v___x_5437_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(
                    v_snd_5424_,
                    v_hyp_5425_,
                    v___y_5432_,
                    v___y_5433_,
                    v___y_5434_,
                    v___y_5435_,
                );
                if lean_obj_tag(v___x_5437_) == 0 {
                    v_a_5438_ = lean_ctor_get(v___x_5437_, 0);
                    lean_inc(v_a_5438_);
                    lean_dec_ref_known(v___x_5437_, 1);
                    v___x_5439_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0;
                    v___x_5440_ = lean_st_mk_ref(v___x_5439_);
                    v_focusHyp_5441_ = lean_ctor_get(v_a_5438_, 0);
                    v_restHyps_5442_ = lean_ctor_get(v_a_5438_, 1);
                    v_u_5443_ = lean_ctor_get(v_snd_5424_, 0);
                    v_00_u03c3s_5444_ = lean_ctor_get(v_snd_5424_, 1);
                    v_target_5445_ = lean_ctor_get(v_snd_5424_, 3);
                    lean_inc_ref(v_restHyps_5442_);
                    lean_inc_ref(v_target_5445_);
                    lean_inc_ref_n(v_00_u03c3s_5444_, 2);
                    lean_inc(v___x_5440_);
                    lean_inc_n(v_u_5443_, 2);
                    v___x_5446_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed
                            as *mut core::ffi::c_void,
                        11,
                        5,
                    );
                    lean_closure_set(v___x_5446_, 0, v_u_5443_);
                    lean_closure_set(v___x_5446_, 1, v___x_5440_);
                    lean_closure_set(v___x_5446_, 2, v_00_u03c3s_5444_);
                    lean_closure_set(v___x_5446_, 3, v_target_5445_);
                    lean_closure_set(v___x_5446_, 4, v_restHyps_5442_);
                    lean_inc_ref(v_focusHyp_5441_);
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
                    if lean_obj_tag(v___x_5447_) == 0 {
                        v_a_5448_ = lean_ctor_get(v___x_5447_, 0);
                        lean_inc(v_a_5448_);
                        lean_dec_ref_known(v___x_5447_, 1);
                        v_snd_5449_ = lean_ctor_get(v_a_5448_, 1);
                        lean_inc(v_snd_5449_);
                        lean_dec(v_a_5448_);
                        v_snd_5450_ = lean_ctor_get(v_snd_5449_, 1);
                        lean_inc(v_snd_5450_);
                        lean_dec(v_snd_5449_);
                        v___x_5451_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(
                            v_a_5438_,
                            v_snd_5424_,
                            v_snd_5450_,
                        );
                        v___x_5452_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_fst_5427_, v___x_5451_, v___y_5433_);
                        lean_dec_ref(v___x_5452_);
                        v___x_5453_ = lean_st_ref_get(v___x_5440_);
                        lean_dec(v___x_5440_);
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
                        lean_dec(v___x_5440_);
                        lean_dec(v_a_5438_);
                        lean_dec(v_fst_5427_);
                        lean_dec_ref(v_snd_5424_);
                        v_a_5456_ = lean_ctor_get(v___x_5447_, 0);
                        v_isSharedCheck_5463_ = (!lean_is_exclusive(v___x_5447_)) as u8;
                        if v_isSharedCheck_5463_ == 0 {
                            v___x_5458_ = v___x_5447_;
                            v_isShared_5459_ = v_isSharedCheck_5463_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5456_);
                            lean_dec(v___x_5447_);
                            v___x_5458_ = lean_box(0);
                            v_isShared_5459_ = v_isSharedCheck_5463_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fst_5427_);
                    lean_dec(v_a_5426_);
                    lean_dec_ref(v_snd_5424_);
                    v_a_5464_ = lean_ctor_get(v___x_5437_, 0);
                    v_isSharedCheck_5471_ = (!lean_is_exclusive(v___x_5437_)) as u8;
                    if v_isSharedCheck_5471_ == 0 {
                        v___x_5466_ = v___x_5437_;
                        v_isShared_5467_ = v_isSharedCheck_5471_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5464_);
                        lean_dec(v___x_5437_);
                        v___x_5466_ = lean_box(0);
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
                    v_reuseFailAlloc_5462_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_a_5456_);
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
                    v_reuseFailAlloc_5470_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5464_);
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
    mut v_snd_5472_: *mut LeanObject,
    mut v_hyp_5473_: *mut LeanObject,
    mut v_a_5474_: *mut LeanObject,
    mut v_fst_5475_: *mut LeanObject,
    mut v___y_5476_: *mut LeanObject,
    mut v___y_5477_: *mut LeanObject,
    mut v___y_5478_: *mut LeanObject,
    mut v___y_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
    mut v___y_5484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5485_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5483_);
    lean_dec_ref(v___y_5482_);
    lean_dec(v___y_5481_);
    lean_dec_ref(v___y_5480_);
    lean_dec(v___y_5479_);
    lean_dec_ref(v___y_5478_);
    lean_dec(v___y_5477_);
    lean_dec_ref(v___y_5476_);
    return v_res_5485_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: f64 = 0.0;
    v___x_5486_ = lean_unsigned_to_nat(0);
    v___x_5487_ = lean_float_of_nat(v___x_5486_);
    return v___x_5487_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(
    mut v_cls_5491_: *mut LeanObject,
    mut v_msg_5492_: *mut LeanObject,
    mut v___y_5493_: *mut LeanObject,
    mut v___y_5494_: *mut LeanObject,
    mut v___y_5495_: *mut LeanObject,
    mut v___y_5496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5503_: u8 = 0;
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5516_: u8 = 0;
    let mut v_tid_5517_: u64 = 0;
    let mut v_traces_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5521_: u8 = 0;
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: f64 = 0.0;
    let mut v___x_5524_: u8 = 0;
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5542_: u8 = 0;
    let mut v_isSharedCheck_5543_: u8 = 0;
    let mut v_isSharedCheck_5544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5498_ = lean_ctor_get(v___y_5495_, 5);
                v___x_5499_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
                v_a_5500_ = lean_ctor_get(v___x_5499_, 0);
                v_isSharedCheck_5544_ = (!lean_is_exclusive(v___x_5499_)) as u8;
                if v_isSharedCheck_5544_ == 0 {
                    v___x_5502_ = v___x_5499_;
                    v_isShared_5503_ = v_isSharedCheck_5544_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5500_);
                    lean_dec(v___x_5499_);
                    v___x_5502_ = lean_box(0);
                    v_isShared_5503_ = v_isSharedCheck_5544_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5504_ = lean_st_ref_take(v___y_5496_);
                v_traceState_5505_ = lean_ctor_get(v___x_5504_, 4);
                v_env_5506_ = lean_ctor_get(v___x_5504_, 0);
                v_nextMacroScope_5507_ = lean_ctor_get(v___x_5504_, 1);
                v_ngen_5508_ = lean_ctor_get(v___x_5504_, 2);
                v_auxDeclNGen_5509_ = lean_ctor_get(v___x_5504_, 3);
                v_cache_5510_ = lean_ctor_get(v___x_5504_, 5);
                v_messages_5511_ = lean_ctor_get(v___x_5504_, 6);
                v_infoState_5512_ = lean_ctor_get(v___x_5504_, 7);
                v_snapshotTasks_5513_ = lean_ctor_get(v___x_5504_, 8);
                v_isSharedCheck_5543_ = (!lean_is_exclusive(v___x_5504_)) as u8;
                if v_isSharedCheck_5543_ == 0 {
                    v___x_5515_ = v___x_5504_;
                    v_isShared_5516_ = v_isSharedCheck_5543_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5513_);
                    lean_inc(v_infoState_5512_);
                    lean_inc(v_messages_5511_);
                    lean_inc(v_cache_5510_);
                    lean_inc(v_traceState_5505_);
                    lean_inc(v_auxDeclNGen_5509_);
                    lean_inc(v_ngen_5508_);
                    lean_inc(v_nextMacroScope_5507_);
                    lean_inc(v_env_5506_);
                    lean_dec(v___x_5504_);
                    v___x_5515_ = lean_box(0);
                    v_isShared_5516_ = v_isSharedCheck_5543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5517_ = lean_ctor_get_uint64(
                    v_traceState_5505_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_5518_ = lean_ctor_get(v_traceState_5505_, 0);
                v_isSharedCheck_5542_ = (!lean_is_exclusive(v_traceState_5505_)) as u8;
                if v_isSharedCheck_5542_ == 0 {
                    v___x_5520_ = v_traceState_5505_;
                    v_isShared_5521_ = v_isSharedCheck_5542_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_5518_);
                    lean_dec(v_traceState_5505_);
                    v___x_5520_ = lean_box(0);
                    v_isShared_5521_ = v_isSharedCheck_5542_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5522_ = lean_box(0);
                v___x_5523_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0);
                v___x_5524_ = 0;
                v___x_5525_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1;
                v___x_5526_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_5526_, 0, v_cls_5491_);
                lean_ctor_set(v___x_5526_, 1, v___x_5522_);
                lean_ctor_set(v___x_5526_, 2, v___x_5525_);
                lean_ctor_set_float(
                    v___x_5526_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5523_,
                );
                lean_ctor_set_float(
                    v___x_5526_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_5523_,
                );
                lean_ctor_set_uint8(
                    v___x_5526_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_5524_,
                );
                v___x_5527_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2;
                v___x_5528_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_5528_, 0, v___x_5526_);
                lean_ctor_set(v___x_5528_, 1, v_a_5500_);
                lean_ctor_set(v___x_5528_, 2, v___x_5527_);
                lean_inc(v_ref_5498_);
                v___x_5529_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5529_, 0, v_ref_5498_);
                lean_ctor_set(v___x_5529_, 1, v___x_5528_);
                v___x_5530_ = l_Lean_PersistentArray_push___redArg(v_traces_5518_, v___x_5529_);
                if v_isShared_5521_ == 0 {
                    lean_ctor_set(v___x_5520_, 0, v___x_5530_);
                    v___x_5532_ = v___x_5520_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5541_, 0, v___x_5530_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5541_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5517_,
                    );
                    v___x_5532_ = v_reuseFailAlloc_5541_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5516_ == 0 {
                    lean_ctor_set(v___x_5515_, 4, v___x_5532_);
                    v___x_5534_ = v___x_5515_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5540_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5540_, 0, v_env_5506_);
                    lean_ctor_set(v_reuseFailAlloc_5540_, 1, v_nextMacroScope_5507_);
                    lean_ctor_set(v_reuseFailAlloc_5540_, 2, v_ngen_5508_);
                    lean_ctor_set(v_reuseFailAlloc_5540_, 3, v_auxDeclNGen_5509_);
                    lean_ctor_set(v_reuseFailAlloc_5540_, 4, v___x_5532_);
                    lean_ctor_set(v_reuseFailAlloc_5540_, 5, v_cache_5510_);
                    lean_ctor_set(v_reuseFailAlloc_5540_, 6, v_messages_5511_);
                    lean_ctor_set(v_reuseFailAlloc_5540_, 7, v_infoState_5512_);
                    lean_ctor_set(v_reuseFailAlloc_5540_, 8, v_snapshotTasks_5513_);
                    v___x_5534_ = v_reuseFailAlloc_5540_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5535_ = lean_st_ref_set(v___y_5496_, v___x_5534_);
                v___x_5536_ = lean_box(0);
                if v_isShared_5503_ == 0 {
                    lean_ctor_set(v___x_5502_, 0, v___x_5536_);
                    v___x_5538_ = v___x_5502_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5539_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5539_, 0, v___x_5536_);
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
    mut v_cls_5545_: *mut LeanObject,
    mut v_msg_5546_: *mut LeanObject,
    mut v___y_5547_: *mut LeanObject,
    mut v___y_5548_: *mut LeanObject,
    mut v___y_5549_: *mut LeanObject,
    mut v___y_5550_: *mut LeanObject,
    mut v___y_5551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5552_: *mut LeanObject = core::ptr::null_mut();
    v_res_5552_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_5545_, v_msg_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
    lean_dec(v___y_5550_);
    lean_dec_ref(v___y_5549_);
    lean_dec(v___y_5548_);
    lean_dec_ref(v___y_5547_);
    return v_res_5552_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(
    mut v_as_5556_: *mut LeanObject,
    mut v___y_5557_: *mut LeanObject,
    mut v___y_5558_: *mut LeanObject,
    mut v___y_5559_: *mut LeanObject,
    mut v___y_5560_: *mut LeanObject,
    mut v___y_5561_: *mut LeanObject,
    mut v___y_5562_: *mut LeanObject,
    mut v___y_5563_: *mut LeanObject,
    mut v___y_5564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5569_: u8 = 0;
    let mut v_tail_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: u8 = 0;
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_5556_) == 0 {
                    v___x_5566_ = lean_box(0);
                    v___x_5567_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5567_, 0, v___x_5566_);
                    return v___x_5567_;
                } else {
                    v_options_5568_ = lean_ctor_get(v___y_5563_, 2);
                    v_hasTrace_5569_ = lean_ctor_get_uint8(
                        v_options_5568_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5569_ == 0 {
                        v_tail_5570_ = lean_ctor_get(v_as_5556_, 1);
                        lean_inc(v_tail_5570_);
                        lean_dec_ref_known(v_as_5556_, 2);
                        v_as_5556_ = v_tail_5570_;
                        state = 0;
                        continue;
                    } else {
                        v_head_5572_ = lean_ctor_get(v_as_5556_, 0);
                        lean_inc(v_head_5572_);
                        v_tail_5573_ = lean_ctor_get(v_as_5556_, 1);
                        lean_inc(v_tail_5573_);
                        lean_dec_ref_known(v_as_5556_, 2);
                        v_fst_5574_ = lean_ctor_get(v_head_5572_, 0);
                        lean_inc_n(v_fst_5574_, 2);
                        v_snd_5575_ = lean_ctor_get(v_head_5572_, 1);
                        lean_inc(v_snd_5575_);
                        lean_dec(v_head_5572_);
                        v_inheritedTraceOptions_5576_ = lean_ctor_get(v___y_5563_, 13);
                        v___x_5577_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1;
                        v___x_5578_ = l_Lean_Name_append(v___x_5577_, v_fst_5574_);
                        v___x_5579_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5576_,
                            v_options_5568_,
                            v___x_5578_,
                        );
                        lean_dec(v___x_5578_);
                        if v___x_5579_ == 0 {
                            lean_dec(v_snd_5575_);
                            lean_dec(v_fst_5574_);
                            v_as_5556_ = v_tail_5573_;
                            state = 0;
                            continue;
                        } else {
                            v___x_5581_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_5581_, 0, v_snd_5575_);
                            v___x_5582_ = l_Lean_MessageData_ofFormat(v___x_5581_);
                            v___x_5583_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_fst_5574_, v___x_5582_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_);
                            if lean_obj_tag(v___x_5583_) == 0 {
                                lean_dec_ref_known(v___x_5583_, 1);
                                v_as_5556_ = v_tail_5573_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_tail_5573_);
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
    mut v_as_5585_: *mut LeanObject,
    mut v___y_5586_: *mut LeanObject,
    mut v___y_5587_: *mut LeanObject,
    mut v___y_5588_: *mut LeanObject,
    mut v___y_5589_: *mut LeanObject,
    mut v___y_5590_: *mut LeanObject,
    mut v___y_5591_: *mut LeanObject,
    mut v___y_5592_: *mut LeanObject,
    mut v___y_5593_: *mut LeanObject,
    mut v___y_5594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5595_: *mut LeanObject = core::ptr::null_mut();
    v_res_5595_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v_as_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
    lean_dec(v___y_5593_);
    lean_dec_ref(v___y_5592_);
    lean_dec(v___y_5591_);
    lean_dec_ref(v___y_5590_);
    lean_dec(v___y_5589_);
    lean_dec_ref(v___y_5588_);
    lean_dec(v___y_5587_);
    lean_dec_ref(v___y_5586_);
    return v_res_5595_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(
    mut v_x_5596_: *mut LeanObject,
    mut v___y_5597_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5596_) == 0 {
        let mut v_a_5598_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
        v_a_5598_ = lean_ctor_get(v_x_5596_, 0);
        lean_inc(v_a_5598_);
        v___x_5599_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5599_, 0, v_a_5598_);
        lean_ctor_set(v___x_5599_, 1, v___y_5597_);
        return v___x_5599_;
    } else {
        let mut v_a_5600_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
        v_a_5600_ = lean_ctor_get(v_x_5596_, 0);
        lean_inc(v_a_5600_);
        v___x_5601_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5601_, 0, v_a_5600_);
        lean_ctor_set(v___x_5601_, 1, v___y_5597_);
        return v___x_5601_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(
    mut v_x_5602_: *mut LeanObject,
    mut v___y_5603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5604_: *mut LeanObject = core::ptr::null_mut();
    v_res_5604_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_5602_, v___y_5603_);
    lean_dec_ref(v_x_5602_);
    return v_res_5604_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(
    mut v_env_5605_: *mut LeanObject,
    mut v_stx_5606_: *mut LeanObject,
    mut v___y_5607_: *mut LeanObject,
    mut v___y_5608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5614_: u8 = 0;
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5619_: u8 = 0;
    let mut v_unused_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v_snd_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5630_: u8 = 0;
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5635_: u8 = 0;
    let mut v_a_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5640_: u8 = 0;
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5648_: u8 = 0;
    let mut v_isSharedCheck_5649_: u8 = 0;
    let mut v_a_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5654_: u8 = 0;
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5657_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_5609_) == 0 {
                    v_a_5610_ = lean_ctor_get(v___x_5609_, 0);
                    lean_inc(v_a_5610_);
                    if lean_obj_tag(v_a_5610_) == 0 {
                        v_a_5611_ = lean_ctor_get(v___x_5609_, 1);
                        v_isSharedCheck_5619_ = (!lean_is_exclusive(v___x_5609_)) as u8;
                        if v_isSharedCheck_5619_ == 0 {
                            v_unused_5620_ = lean_ctor_get(v___x_5609_, 0);
                            lean_dec(v_unused_5620_);
                            v___x_5613_ = v___x_5609_;
                            v_isShared_5614_ = v_isSharedCheck_5619_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5611_);
                            lean_dec(v___x_5609_);
                            v___x_5613_ = lean_box(0);
                            v_isShared_5614_ = v_isSharedCheck_5619_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_5621_ = lean_ctor_get(v_a_5610_, 0);
                        v_isSharedCheck_5649_ = (!lean_is_exclusive(v_a_5610_)) as u8;
                        if v_isSharedCheck_5649_ == 0 {
                            v___x_5623_ = v_a_5610_;
                            v_isShared_5624_ = v_isSharedCheck_5649_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_5621_);
                            lean_dec(v_a_5610_);
                            v___x_5623_ = lean_box(0);
                            v_isShared_5624_ = v_isSharedCheck_5649_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_5650_ = lean_ctor_get(v___x_5609_, 0);
                    v_a_5651_ = lean_ctor_get(v___x_5609_, 1);
                    v_isSharedCheck_5658_ = (!lean_is_exclusive(v___x_5609_)) as u8;
                    if v_isSharedCheck_5658_ == 0 {
                        v___x_5653_ = v___x_5609_;
                        v_isShared_5654_ = v_isSharedCheck_5658_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5651_);
                        lean_inc(v_a_5650_);
                        lean_dec(v___x_5609_);
                        v___x_5653_ = lean_box(0);
                        v_isShared_5654_ = v_isSharedCheck_5658_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5615_ = lean_box(0);
                if v_isShared_5614_ == 0 {
                    lean_ctor_set(v___x_5613_, 0, v___x_5615_);
                    v___x_5617_ = v___x_5613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5618_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5618_, 0, v___x_5615_);
                    lean_ctor_set(v_reuseFailAlloc_5618_, 1, v_a_5611_);
                    v___x_5617_ = v_reuseFailAlloc_5618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5617_;
            }
            3 => {
                v_snd_5625_ = lean_ctor_get(v_val_5621_, 1);
                lean_inc(v_snd_5625_);
                lean_dec(v_val_5621_);
                if lean_obj_tag(v_snd_5625_) == 0 {
                    lean_del_object(v___x_5623_);
                    v_a_5626_ = lean_ctor_get(v___x_5609_, 1);
                    lean_inc(v_a_5626_);
                    lean_dec_ref_known(v___x_5609_, 2);
                    v_a_5627_ = lean_ctor_get(v_snd_5625_, 0);
                    v_isSharedCheck_5635_ = (!lean_is_exclusive(v_snd_5625_)) as u8;
                    if v_isSharedCheck_5635_ == 0 {
                        v___x_5629_ = v_snd_5625_;
                        v_isShared_5630_ = v_isSharedCheck_5635_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5627_);
                        lean_dec(v_snd_5625_);
                        v___x_5629_ = lean_box(0);
                        v_isShared_5630_ = v_isSharedCheck_5635_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_5636_ = lean_ctor_get(v___x_5609_, 1);
                    lean_inc(v_a_5636_);
                    lean_dec_ref_known(v___x_5609_, 2);
                    v_a_5637_ = lean_ctor_get(v_snd_5625_, 0);
                    v_isSharedCheck_5648_ = (!lean_is_exclusive(v_snd_5625_)) as u8;
                    if v_isSharedCheck_5648_ == 0 {
                        v___x_5639_ = v_snd_5625_;
                        v_isShared_5640_ = v_isSharedCheck_5648_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5637_);
                        lean_dec(v_snd_5625_);
                        v___x_5639_ = lean_box(0);
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
                    v_reuseFailAlloc_5634_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_a_5627_);
                    v___x_5632_ = v_reuseFailAlloc_5634_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5633_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_5632_, v_a_5626_);
                lean_dec_ref(v___x_5632_);
                return v___x_5633_;
            }
            6 => {
                if v_isShared_5624_ == 0 {
                    lean_ctor_set(v___x_5623_, 0, v_a_5637_);
                    v___x_5642_ = v___x_5623_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5647_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5647_, 0, v_a_5637_);
                    v___x_5642_ = v_reuseFailAlloc_5647_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5640_ == 0 {
                    lean_ctor_set(v___x_5639_, 0, v___x_5642_);
                    v___x_5644_ = v___x_5639_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5646_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5646_, 0, v___x_5642_);
                    v___x_5644_ = v_reuseFailAlloc_5646_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5645_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_5644_, v_a_5636_);
                lean_dec_ref(v___x_5644_);
                return v___x_5645_;
            }
            9 => {
                if v_isShared_5654_ == 0 {
                    v___x_5656_ = v___x_5653_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5657_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5650_);
                    lean_ctor_set(v_reuseFailAlloc_5657_, 1, v_a_5651_);
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
    mut v_env_5659_: *mut LeanObject,
    mut v_stx_5660_: *mut LeanObject,
    mut v___y_5661_: *mut LeanObject,
    mut v___y_5662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5663_: *mut LeanObject = core::ptr::null_mut();
    v_res_5663_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(v_env_5659_, v_stx_5660_, v___y_5661_, v___y_5662_);
    lean_dec_ref(v___y_5661_);
    return v_res_5663_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(
    mut v_msg_5664_: *mut LeanObject,
    mut v___y_5665_: *mut LeanObject,
    mut v___y_5666_: *mut LeanObject,
    mut v___y_5667_: *mut LeanObject,
    mut v___y_5668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5675_: u8 = 0;
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5680_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5670_ = lean_ctor_get(v___y_5667_, 5);
                v___x_5671_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_);
                v_a_5672_ = lean_ctor_get(v___x_5671_, 0);
                v_isSharedCheck_5680_ = (!lean_is_exclusive(v___x_5671_)) as u8;
                if v_isSharedCheck_5680_ == 0 {
                    v___x_5674_ = v___x_5671_;
                    v_isShared_5675_ = v_isSharedCheck_5680_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5672_);
                    lean_dec(v___x_5671_);
                    v___x_5674_ = lean_box(0);
                    v_isShared_5675_ = v_isSharedCheck_5680_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5670_);
                v___x_5676_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5676_, 0, v_ref_5670_);
                lean_ctor_set(v___x_5676_, 1, v_a_5672_);
                if v_isShared_5675_ == 0 {
                    lean_ctor_set_tag(v___x_5674_, 1);
                    lean_ctor_set(v___x_5674_, 0, v___x_5676_);
                    v___x_5678_ = v___x_5674_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5679_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5679_, 0, v___x_5676_);
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
    mut v_msg_5681_: *mut LeanObject,
    mut v___y_5682_: *mut LeanObject,
    mut v___y_5683_: *mut LeanObject,
    mut v___y_5684_: *mut LeanObject,
    mut v___y_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5687_: *mut LeanObject = core::ptr::null_mut();
    v_res_5687_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
    lean_dec(v___y_5685_);
    lean_dec_ref(v___y_5684_);
    lean_dec(v___y_5683_);
    lean_dec_ref(v___y_5682_);
    return v_res_5687_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(
    mut v_ref_5688_: *mut LeanObject,
    mut v_msg_5689_: *mut LeanObject,
    mut v___y_5690_: *mut LeanObject,
    mut v___y_5691_: *mut LeanObject,
    mut v___y_5692_: *mut LeanObject,
    mut v___y_5693_: *mut LeanObject,
    mut v___y_5694_: *mut LeanObject,
    mut v___y_5695_: *mut LeanObject,
    mut v___y_5696_: *mut LeanObject,
    mut v___y_5697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5711_: u8 = 0;
    let mut v_cancelTk_x3f_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5713_: u8 = 0;
    let mut v_inheritedTraceOptions_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_5699_ = lean_ctor_get(v___y_5696_, 0);
    v_fileMap_5700_ = lean_ctor_get(v___y_5696_, 1);
    v_options_5701_ = lean_ctor_get(v___y_5696_, 2);
    v_currRecDepth_5702_ = lean_ctor_get(v___y_5696_, 3);
    v_maxRecDepth_5703_ = lean_ctor_get(v___y_5696_, 4);
    v_ref_5704_ = lean_ctor_get(v___y_5696_, 5);
    v_currNamespace_5705_ = lean_ctor_get(v___y_5696_, 6);
    v_openDecls_5706_ = lean_ctor_get(v___y_5696_, 7);
    v_initHeartbeats_5707_ = lean_ctor_get(v___y_5696_, 8);
    v_maxHeartbeats_5708_ = lean_ctor_get(v___y_5696_, 9);
    v_quotContext_5709_ = lean_ctor_get(v___y_5696_, 10);
    v_currMacroScope_5710_ = lean_ctor_get(v___y_5696_, 11);
    v_diag_5711_ = lean_ctor_get_uint8(
        v___y_5696_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5712_ = lean_ctor_get(v___y_5696_, 12);
    v_suppressElabErrors_5713_ = lean_ctor_get_uint8(
        v___y_5696_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5714_ = lean_ctor_get(v___y_5696_, 13);
    v_ref_5715_ = l_Lean_replaceRef(v_ref_5688_, v_ref_5704_);
    lean_inc_ref(v_inheritedTraceOptions_5714_);
    lean_inc(v_cancelTk_x3f_5712_);
    lean_inc(v_currMacroScope_5710_);
    lean_inc(v_quotContext_5709_);
    lean_inc(v_maxHeartbeats_5708_);
    lean_inc(v_initHeartbeats_5707_);
    lean_inc(v_openDecls_5706_);
    lean_inc(v_currNamespace_5705_);
    lean_inc(v_maxRecDepth_5703_);
    lean_inc(v_currRecDepth_5702_);
    lean_inc_ref(v_options_5701_);
    lean_inc_ref(v_fileMap_5700_);
    lean_inc_ref(v_fileName_5699_);
    v___x_5716_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_5716_, 0, v_fileName_5699_);
    lean_ctor_set(v___x_5716_, 1, v_fileMap_5700_);
    lean_ctor_set(v___x_5716_, 2, v_options_5701_);
    lean_ctor_set(v___x_5716_, 3, v_currRecDepth_5702_);
    lean_ctor_set(v___x_5716_, 4, v_maxRecDepth_5703_);
    lean_ctor_set(v___x_5716_, 5, v_ref_5715_);
    lean_ctor_set(v___x_5716_, 6, v_currNamespace_5705_);
    lean_ctor_set(v___x_5716_, 7, v_openDecls_5706_);
    lean_ctor_set(v___x_5716_, 8, v_initHeartbeats_5707_);
    lean_ctor_set(v___x_5716_, 9, v_maxHeartbeats_5708_);
    lean_ctor_set(v___x_5716_, 10, v_quotContext_5709_);
    lean_ctor_set(v___x_5716_, 11, v_currMacroScope_5710_);
    lean_ctor_set(v___x_5716_, 12, v_cancelTk_x3f_5712_);
    lean_ctor_set(v___x_5716_, 13, v_inheritedTraceOptions_5714_);
    lean_ctor_set_uint8(
        v___x_5716_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_5711_,
    );
    lean_ctor_set_uint8(
        v___x_5716_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5713_,
    );
    v___x_5717_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_5689_, v___y_5694_, v___y_5695_, v___x_5716_, v___y_5697_);
    lean_dec_ref_known(v___x_5716_, 14);
    return v___x_5717_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg___boxed(
    mut v_ref_5718_: *mut LeanObject,
    mut v_msg_5719_: *mut LeanObject,
    mut v___y_5720_: *mut LeanObject,
    mut v___y_5721_: *mut LeanObject,
    mut v___y_5722_: *mut LeanObject,
    mut v___y_5723_: *mut LeanObject,
    mut v___y_5724_: *mut LeanObject,
    mut v___y_5725_: *mut LeanObject,
    mut v___y_5726_: *mut LeanObject,
    mut v___y_5727_: *mut LeanObject,
    mut v___y_5728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5729_: *mut LeanObject = core::ptr::null_mut();
    v_res_5729_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_5718_, v_msg_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_);
    lean_dec(v___y_5727_);
    lean_dec_ref(v___y_5726_);
    lean_dec(v___y_5725_);
    lean_dec_ref(v___y_5724_);
    lean_dec(v___y_5723_);
    lean_dec_ref(v___y_5722_);
    lean_dec(v___y_5721_);
    lean_dec_ref(v___y_5720_);
    lean_dec(v_ref_5718_);
    return v_res_5729_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(
    mut v_env_5730_: *mut LeanObject,
    mut v_options_5731_: *mut LeanObject,
    mut v_currNamespace_5732_: *mut LeanObject,
    mut v_openDecls_5733_: *mut LeanObject,
    mut v_n_5734_: *mut LeanObject,
    mut v___y_5735_: *mut LeanObject,
    mut v___y_5736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    v___x_5737_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_5730_,
        v_options_5731_,
        v_currNamespace_5732_,
        v_openDecls_5733_,
        v_n_5734_,
    );
    v___x_5738_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5738_, 0, v___x_5737_);
    lean_ctor_set(v___x_5738_, 1, v___y_5736_);
    return v___x_5738_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(
    mut v_env_5739_: *mut LeanObject,
    mut v_options_5740_: *mut LeanObject,
    mut v_currNamespace_5741_: *mut LeanObject,
    mut v_openDecls_5742_: *mut LeanObject,
    mut v_n_5743_: *mut LeanObject,
    mut v___y_5744_: *mut LeanObject,
    mut v___y_5745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5746_: *mut LeanObject = core::ptr::null_mut();
    v_res_5746_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(v_env_5739_, v_options_5740_, v_currNamespace_5741_, v_openDecls_5742_, v_n_5743_, v___y_5744_, v___y_5745_);
    lean_dec_ref(v___y_5744_);
    lean_dec_ref(v_options_5740_);
    return v_res_5746_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(
    mut v_currNamespace_5747_: *mut LeanObject,
    mut v___y_5748_: *mut LeanObject,
    mut v___y_5749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    v___x_5750_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5750_, 0, v_currNamespace_5747_);
    lean_ctor_set(v___x_5750_, 1, v___y_5749_);
    return v___x_5750_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(
    mut v_currNamespace_5751_: *mut LeanObject,
    mut v___y_5752_: *mut LeanObject,
    mut v___y_5753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5754_: *mut LeanObject = core::ptr::null_mut();
    v_res_5754_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(v_currNamespace_5751_, v___y_5752_, v___y_5753_);
    lean_dec_ref(v___y_5752_);
    return v_res_5754_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    v___x_5760_ = l_Lean_maxRecDepthErrorMessage;
    v___x_5761_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_5761_, 0, v___x_5760_);
    return v___x_5761_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    v___x_5762_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3);
    v___x_5763_ = l_Lean_MessageData_ofFormat(v___x_5762_);
    return v___x_5763_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    v___x_5764_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4);
    v___x_5765_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2;
    v___x_5766_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_5766_, 0, v___x_5765_);
    lean_ctor_set(v___x_5766_, 1, v___x_5764_);
    return v___x_5766_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(
    mut v_ref_5767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    v___x_5769_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5);
    v___x_5770_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5770_, 0, v_ref_5767_);
    lean_ctor_set(v___x_5770_, 1, v___x_5769_);
    v___x_5771_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5771_, 0, v___x_5770_);
    return v___x_5771_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___boxed(
    mut v_ref_5772_: *mut LeanObject,
    mut v___y_5773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5774_: *mut LeanObject = core::ptr::null_mut();
    v_res_5774_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_5772_);
    return v_res_5774_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(
    mut v_env_5775_: *mut LeanObject,
    mut v_currNamespace_5776_: *mut LeanObject,
    mut v_openDecls_5777_: *mut LeanObject,
    mut v_n_5778_: *mut LeanObject,
    mut v___y_5779_: *mut LeanObject,
    mut v___y_5780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    v___x_5781_ = l_Lean_ResolveName_resolveNamespace(
        v_env_5775_,
        v_currNamespace_5776_,
        v_openDecls_5777_,
        v_n_5778_,
    );
    v___x_5782_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5782_, 0, v___x_5781_);
    lean_ctor_set(v___x_5782_, 1, v___y_5780_);
    return v___x_5782_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(
    mut v_env_5783_: *mut LeanObject,
    mut v_currNamespace_5784_: *mut LeanObject,
    mut v_openDecls_5785_: *mut LeanObject,
    mut v_n_5786_: *mut LeanObject,
    mut v___y_5787_: *mut LeanObject,
    mut v___y_5788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5789_: *mut LeanObject = core::ptr::null_mut();
    v_res_5789_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(v_env_5783_, v_currNamespace_5784_, v_openDecls_5785_, v_n_5786_, v___y_5787_, v___y_5788_);
    lean_dec_ref(v___y_5787_);
    return v_res_5789_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(
    mut v_keys_5790_: *mut LeanObject,
    mut v_i_5791_: *mut LeanObject,
    mut v_k_5792_: *mut LeanObject,
) -> u8 {
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: u8 = 0;
    let mut v_k_x27_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: u8 = 0;
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5793_ = lean_array_get_size(v_keys_5790_);
                v___x_5794_ = lean_nat_dec_lt(v_i_5791_, v___x_5793_);
                if v___x_5794_ == 0 {
                    lean_dec(v_i_5791_);
                    return v___x_5794_;
                } else {
                    v_k_x27_5795_ = lean_array_fget_borrowed(v_keys_5790_, v_i_5791_);
                    v___x_5796_ = l_Lean_instBEqExtraModUse_beq(v_k_5792_, v_k_x27_5795_);
                    if v___x_5796_ == 0 {
                        v___x_5797_ = lean_unsigned_to_nat(1);
                        v___x_5798_ = lean_nat_add(v_i_5791_, v___x_5797_);
                        lean_dec(v_i_5791_);
                        v_i_5791_ = v___x_5798_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_5791_);
                        return v___x_5796_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg___boxed(
    mut v_keys_5800_: *mut LeanObject,
    mut v_i_5801_: *mut LeanObject,
    mut v_k_5802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5803_: u8 = 0;
    let mut v_r_5804_: *mut LeanObject = core::ptr::null_mut();
    v_res_5803_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_5800_, v_i_5801_, v_k_5802_);
    lean_dec_ref(v_k_5802_);
    lean_dec_ref(v_keys_5800_);
    v_r_5804_ = lean_box((v_res_5803_) as usize);
    return v_r_5804_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(
    mut v_x_5805_: *mut LeanObject,
    mut v_x_5806_: usize,
    mut v_x_5807_: *mut LeanObject,
) -> u8 {
    let mut v_es_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: usize = 0;
    let mut v___x_5811_: usize = 0;
    let mut v___x_5812_: usize = 0;
    let mut v_j_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: u8 = 0;
    let mut v_node_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: usize = 0;
    let mut v___x_5820_: u8 = 0;
    let mut v_ks_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5805_) == 0 {
                    v_es_5808_ = lean_ctor_get(v_x_5805_, 0);
                    v___x_5809_ = lean_box(2);
                    v___x_5810_ = 5usize;
                    v___x_5811_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1);
                    v___x_5812_ = lean_usize_land(v_x_5806_, v___x_5811_);
                    v_j_5813_ = lean_usize_to_nat(v___x_5812_);
                    v___x_5814_ = lean_array_get_borrowed(v___x_5809_, v_es_5808_, v_j_5813_);
                    lean_dec(v_j_5813_);
                    match lean_obj_tag(v___x_5814_) {
                        0 => {
                            v_key_5815_ = lean_ctor_get(v___x_5814_, 0);
                            v___x_5816_ = l_Lean_instBEqExtraModUse_beq(v_x_5807_, v_key_5815_);
                            return v___x_5816_;
                        }
                        1 => {
                            v_node_5817_ = lean_ctor_get(v___x_5814_, 0);
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
                    v_ks_5821_ = lean_ctor_get(v_x_5805_, 0);
                    v___x_5822_ = lean_unsigned_to_nat(0);
                    v___x_5823_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_ks_5821_, v___x_5822_, v_x_5807_);
                    return v___x_5823_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg___boxed(
    mut v_x_5824_: *mut LeanObject,
    mut v_x_5825_: *mut LeanObject,
    mut v_x_5826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_21359__boxed_5827_: usize = 0;
    let mut v_res_5828_: u8 = 0;
    let mut v_r_5829_: *mut LeanObject = core::ptr::null_mut();
    v_x_21359__boxed_5827_ = lean_unbox_usize(v_x_5825_);
    lean_dec(v_x_5825_);
    v_res_5828_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_5824_, v_x_21359__boxed_5827_, v_x_5826_);
    lean_dec_ref(v_x_5826_);
    lean_dec_ref(v_x_5824_);
    v_r_5829_ = lean_box((v_res_5828_) as usize);
    return v_r_5829_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(
    mut v_x_5830_: *mut LeanObject,
    mut v_x_5831_: *mut LeanObject,
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
    mut v_x_5835_: *mut LeanObject,
    mut v_x_5836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5837_: u8 = 0;
    let mut v_r_5838_: *mut LeanObject = core::ptr::null_mut();
    v_res_5837_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_5835_, v_x_5836_);
    lean_dec_ref(v_x_5836_);
    lean_dec_ref(v_x_5835_);
    v_r_5838_ = lean_box((v_res_5837_) as usize);
    return v_r_5838_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2()
-> *mut LeanObject {
    let mut v___x_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut LeanObject = core::ptr::null_mut();
    v___x_5841_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1;
    v___x_5842_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0;
    v___x_5843_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_5842_, v___x_5841_);
    return v___x_5843_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
    v___x_5844_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5844_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4()
-> *mut LeanObject {
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    v___x_5845_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3);
    v___x_5846_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5846_, 0, v___x_5845_);
    return v___x_5846_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5()
-> *mut LeanObject {
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    v___x_5847_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4);
    v___x_5848_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5848_, 0, v___x_5847_);
    lean_ctor_set(v___x_5848_, 1, v___x_5847_);
    return v___x_5848_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6()
-> *mut LeanObject {
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    v___x_5849_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4);
    v___x_5850_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_5850_, 0, v___x_5849_);
    lean_ctor_set(v___x_5850_, 1, v___x_5849_);
    lean_ctor_set(v___x_5850_, 2, v___x_5849_);
    lean_ctor_set(v___x_5850_, 3, v___x_5849_);
    lean_ctor_set(v___x_5850_, 4, v___x_5849_);
    lean_ctor_set(v___x_5850_, 5, v___x_5849_);
    return v___x_5850_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10()
-> *mut LeanObject {
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    v___x_5855_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9;
    v___x_5856_ = l_Lean_stringToMessageData(v___x_5855_);
    return v___x_5856_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12()
-> *mut LeanObject {
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    v___x_5858_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11;
    v___x_5859_ = l_Lean_stringToMessageData(v___x_5858_);
    return v___x_5859_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13()
-> *mut LeanObject {
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    v___x_5860_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1;
    v___x_5861_ = l_Lean_stringToMessageData(v___x_5860_);
    return v___x_5861_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14()
-> *mut LeanObject {
    let mut v_cls_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    v_cls_5862_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8;
    v___x_5863_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1;
    v___x_5864_ = l_Lean_Name_append(v___x_5863_, v_cls_5862_);
    return v___x_5864_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16()
-> *mut LeanObject {
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    v___x_5866_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15;
    v___x_5867_ = l_Lean_stringToMessageData(v___x_5866_);
    return v___x_5867_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18()
-> *mut LeanObject {
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    v___x_5869_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17;
    v___x_5870_ = l_Lean_stringToMessageData(v___x_5869_);
    return v___x_5870_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(
    mut v_mod_5875_: *mut LeanObject,
    mut v_isMeta_5876_: u8,
    mut v_hint_5877_: *mut LeanObject,
    mut v___y_5878_: *mut LeanObject,
    mut v___y_5879_: *mut LeanObject,
    mut v___y_5880_: *mut LeanObject,
    mut v___y_5881_: *mut LeanObject,
    mut v___y_5882_: *mut LeanObject,
    mut v___y_5883_: *mut LeanObject,
    mut v___y_5884_: *mut LeanObject,
    mut v___y_5885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_5889_: u8 = 0;
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5912_: u8 = 0;
    let mut v_asyncMode_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5926_: u8 = 0;
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5934_: u8 = 0;
    let mut v_unused_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5937_: u8 = 0;
    let mut v_unused_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: u8 = 0;
    let mut v_options_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5942_: u8 = 0;
    let mut v_inheritedTraceOptions_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: u8 = 0;
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: u8 = 0;
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5887_ = lean_st_ref_get(v___y_5885_);
                v_env_5888_ = lean_ctor_get(v___x_5887_, 0);
                lean_inc_ref(v_env_5888_);
                lean_dec(v___x_5887_);
                v_isExporting_5889_ = lean_ctor_get_uint8(
                    v_env_5888_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_5888_);
                v___x_5890_ = lean_st_ref_get(v___y_5885_);
                v_env_5891_ = lean_ctor_get(v___x_5890_, 0);
                lean_inc_ref(v_env_5891_);
                lean_dec(v___x_5890_);
                v___x_5892_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2);
                lean_inc(v_mod_5875_);
                v_entry_5893_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v_entry_5893_, 0, v_mod_5875_);
                lean_ctor_set_uint8(
                    v_entry_5893_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_isExporting_5889_,
                );
                lean_ctor_set_uint8(
                    v_entry_5893_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isMeta_5876_,
                );
                v___x_5894_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_5895_ = lean_box(1);
                v___x_5896_ = lean_box(0);
                v___x_5939_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_5892_,
                    v___x_5894_,
                    v_env_5891_,
                    v___x_5895_,
                    v___x_5896_,
                );
                v___x_5940_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v___x_5939_, v_entry_5893_);
                lean_dec(v___x_5939_);
                if v___x_5940_ == 0 {
                    v_options_5941_ = lean_ctor_get(v___y_5884_, 2);
                    v_hasTrace_5942_ = lean_ctor_get_uint8(
                        v_options_5941_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5942_ == 0 {
                        lean_dec(v_hint_5877_);
                        lean_dec(v_mod_5875_);
                        v___y_5898_ = v___y_5883_;
                        v___y_5899_ = v___y_5885_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5943_ = lean_ctor_get(v___y_5884_, 13);
                        v_cls_5944_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8;
                        v___x_5964_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14);
                        v___x_5965_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5943_,
                            v_options_5941_,
                            v___x_5964_,
                        );
                        if v___x_5965_ == 0 {
                            lean_dec(v_hint_5877_);
                            lean_dec(v_mod_5875_);
                            v___y_5898_ = v___y_5883_;
                            v___y_5899_ = v___y_5885_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5966_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16);
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
                    lean_dec_ref_known(v_entry_5893_, 1);
                    lean_dec(v_hint_5877_);
                    lean_dec(v_mod_5875_);
                    v___x_5977_ = lean_box(0);
                    v___x_5978_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5978_, 0, v___x_5977_);
                    return v___x_5978_;
                }
            }
            1 => {
                v___x_5900_ = lean_st_ref_take(v___y_5899_);
                v_toEnvExtension_5901_ = lean_ctor_get(v___x_5894_, 0);
                v_env_5902_ = lean_ctor_get(v___x_5900_, 0);
                v_nextMacroScope_5903_ = lean_ctor_get(v___x_5900_, 1);
                v_ngen_5904_ = lean_ctor_get(v___x_5900_, 2);
                v_auxDeclNGen_5905_ = lean_ctor_get(v___x_5900_, 3);
                v_traceState_5906_ = lean_ctor_get(v___x_5900_, 4);
                v_messages_5907_ = lean_ctor_get(v___x_5900_, 6);
                v_infoState_5908_ = lean_ctor_get(v___x_5900_, 7);
                v_snapshotTasks_5909_ = lean_ctor_get(v___x_5900_, 8);
                v_isSharedCheck_5937_ = (!lean_is_exclusive(v___x_5900_)) as u8;
                if v_isSharedCheck_5937_ == 0 {
                    v_unused_5938_ = lean_ctor_get(v___x_5900_, 5);
                    lean_dec(v_unused_5938_);
                    v___x_5911_ = v___x_5900_;
                    v_isShared_5912_ = v_isSharedCheck_5937_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5909_);
                    lean_inc(v_infoState_5908_);
                    lean_inc(v_messages_5907_);
                    lean_inc(v_traceState_5906_);
                    lean_inc(v_auxDeclNGen_5905_);
                    lean_inc(v_ngen_5904_);
                    lean_inc(v_nextMacroScope_5903_);
                    lean_inc(v_env_5902_);
                    lean_dec(v___x_5900_);
                    v___x_5911_ = lean_box(0);
                    v_isShared_5912_ = v_isSharedCheck_5937_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_5913_ = lean_ctor_get(v_toEnvExtension_5901_, 2);
                v___x_5914_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_5894_,
                    v_env_5902_,
                    v_entry_5893_,
                    v_asyncMode_5913_,
                    v___x_5896_,
                );
                v___x_5915_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5);
                if v_isShared_5912_ == 0 {
                    lean_ctor_set(v___x_5911_, 5, v___x_5915_);
                    lean_ctor_set(v___x_5911_, 0, v___x_5914_);
                    v___x_5917_ = v___x_5911_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5936_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 0, v___x_5914_);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 1, v_nextMacroScope_5903_);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 2, v_ngen_5904_);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 3, v_auxDeclNGen_5905_);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 4, v_traceState_5906_);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 5, v___x_5915_);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 6, v_messages_5907_);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 7, v_infoState_5908_);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 8, v_snapshotTasks_5909_);
                    v___x_5917_ = v_reuseFailAlloc_5936_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5918_ = lean_st_ref_set(v___y_5899_, v___x_5917_);
                v___x_5919_ = lean_st_ref_take(v___y_5898_);
                v_mctx_5920_ = lean_ctor_get(v___x_5919_, 0);
                v_zetaDeltaFVarIds_5921_ = lean_ctor_get(v___x_5919_, 2);
                v_postponed_5922_ = lean_ctor_get(v___x_5919_, 3);
                v_diag_5923_ = lean_ctor_get(v___x_5919_, 4);
                v_isSharedCheck_5934_ = (!lean_is_exclusive(v___x_5919_)) as u8;
                if v_isSharedCheck_5934_ == 0 {
                    v_unused_5935_ = lean_ctor_get(v___x_5919_, 1);
                    lean_dec(v_unused_5935_);
                    v___x_5925_ = v___x_5919_;
                    v_isShared_5926_ = v_isSharedCheck_5934_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_diag_5923_);
                    lean_inc(v_postponed_5922_);
                    lean_inc(v_zetaDeltaFVarIds_5921_);
                    lean_inc(v_mctx_5920_);
                    lean_dec(v___x_5919_);
                    v___x_5925_ = lean_box(0);
                    v_isShared_5926_ = v_isSharedCheck_5934_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5927_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6);
                if v_isShared_5926_ == 0 {
                    lean_ctor_set(v___x_5925_, 1, v___x_5927_);
                    v___x_5929_ = v___x_5925_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5933_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5933_, 0, v_mctx_5920_);
                    lean_ctor_set(v_reuseFailAlloc_5933_, 1, v___x_5927_);
                    lean_ctor_set(v_reuseFailAlloc_5933_, 2, v_zetaDeltaFVarIds_5921_);
                    lean_ctor_set(v_reuseFailAlloc_5933_, 3, v_postponed_5922_);
                    lean_ctor_set(v_reuseFailAlloc_5933_, 4, v_diag_5923_);
                    v___x_5929_ = v_reuseFailAlloc_5933_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5930_ = lean_st_ref_set(v___y_5898_, v___x_5929_);
                v___x_5931_ = lean_box(0);
                v___x_5932_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5932_, 0, v___x_5931_);
                return v___x_5932_;
            }
            6 => {
                v___x_5948_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5948_, 0, v___y_5946_);
                lean_ctor_set(v___x_5948_, 1, v___y_5947_);
                v___x_5949_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_5944_, v___x_5948_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_);
                if lean_obj_tag(v___x_5949_) == 0 {
                    lean_dec_ref_known(v___x_5949_, 1);
                    v___y_5898_ = v___y_5883_;
                    v___y_5899_ = v___y_5885_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_entry_5893_, 1);
                    return v___x_5949_;
                }
            }
            7 => {
                lean_inc_ref(v___y_5952_);
                v___x_5953_ = l_Lean_stringToMessageData(v___y_5952_);
                v___x_5954_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5954_, 0, v___y_5951_);
                lean_ctor_set(v___x_5954_, 1, v___x_5953_);
                v___x_5955_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10);
                v___x_5956_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5956_, 0, v___x_5954_);
                lean_ctor_set(v___x_5956_, 1, v___x_5955_);
                v___x_5957_ = l_Lean_MessageData_ofName(v_mod_5875_);
                v___x_5958_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5958_, 0, v___x_5956_);
                lean_ctor_set(v___x_5958_, 1, v___x_5957_);
                v___x_5959_ = l_Lean_Name_isAnonymous(v_hint_5877_);
                if v___x_5959_ == 0 {
                    v___x_5960_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12);
                    v___x_5961_ = l_Lean_MessageData_ofName(v_hint_5877_);
                    v___x_5962_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5962_, 0, v___x_5960_);
                    lean_ctor_set(v___x_5962_, 1, v___x_5961_);
                    v___y_5946_ = v___x_5958_;
                    v___y_5947_ = v___x_5962_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v_hint_5877_);
                    v___x_5963_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13);
                    v___y_5946_ = v___x_5958_;
                    v___y_5947_ = v___x_5963_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                lean_inc_ref(v___y_5968_);
                v___x_5969_ = l_Lean_stringToMessageData(v___y_5968_);
                v___x_5970_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5970_, 0, v___x_5966_);
                lean_ctor_set(v___x_5970_, 1, v___x_5969_);
                v___x_5971_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18);
                v___x_5972_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5972_, 0, v___x_5970_);
                lean_ctor_set(v___x_5972_, 1, v___x_5971_);
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
    mut v_mod_5979_: *mut LeanObject,
    mut v_isMeta_5980_: *mut LeanObject,
    mut v_hint_5981_: *mut LeanObject,
    mut v___y_5982_: *mut LeanObject,
    mut v___y_5983_: *mut LeanObject,
    mut v___y_5984_: *mut LeanObject,
    mut v___y_5985_: *mut LeanObject,
    mut v___y_5986_: *mut LeanObject,
    mut v___y_5987_: *mut LeanObject,
    mut v___y_5988_: *mut LeanObject,
    mut v___y_5989_: *mut LeanObject,
    mut v___y_5990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_5991_: u8 = 0;
    let mut v_res_5992_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_5991_ = (lean_unbox(v_isMeta_5980_) as u8);
    v_res_5992_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_mod_5979_, v_isMeta_boxed_5991_, v_hint_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_);
    lean_dec(v___y_5989_);
    lean_dec_ref(v___y_5988_);
    lean_dec(v___y_5987_);
    lean_dec_ref(v___y_5986_);
    lean_dec(v___y_5985_);
    lean_dec_ref(v___y_5984_);
    lean_dec(v___y_5983_);
    lean_dec_ref(v___y_5982_);
    return v_res_5992_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(
    mut v_a_5993_: *mut LeanObject,
    mut v_x_5994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: u8 = 0;
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5994_) == 0 {
                    v___x_5995_ = lean_box(0);
                    return v___x_5995_;
                } else {
                    v_key_5996_ = lean_ctor_get(v_x_5994_, 0);
                    v_value_5997_ = lean_ctor_get(v_x_5994_, 1);
                    v_tail_5998_ = lean_ctor_get(v_x_5994_, 2);
                    v___x_5999_ = lean_name_eq(v_key_5996_, v_a_5993_);
                    if v___x_5999_ == 0 {
                        v_x_5994_ = v_tail_5998_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_5997_);
                        v___x_6001_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_6001_, 0, v_value_5997_);
                        return v___x_6001_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg___boxed(
    mut v_a_6002_: *mut LeanObject,
    mut v_x_6003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6004_: *mut LeanObject = core::ptr::null_mut();
    v_res_6004_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_6002_, v_x_6003_);
    lean_dec(v_x_6003_);
    lean_dec(v_a_6002_);
    return v_res_6004_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0()
-> u64 {
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: u64 = 0;
    v___x_6005_ = lean_unsigned_to_nat(1723);
    v___x_6006_ = lean_uint64_of_nat(v___x_6005_);
    return v___x_6006_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(
    mut v_m_6007_: *mut LeanObject,
    mut v_a_6008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: u64 = 0;
    let mut v_hash_6027_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_6009_ = lean_ctor_get(v_m_6007_, 1);
                v___x_6010_ = lean_array_get_size(v_buckets_6009_);
                if lean_obj_tag(v_a_6008_) == 0 {
                    v___x_6026_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0);
                    v___y_6012_ = v___x_6026_;
                    state = 1;
                    continue;
                } else {
                    v_hash_6027_ = lean_ctor_get_uint64(
                        v_a_6008_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_m_6028_: *mut LeanObject,
    mut v_a_6029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6030_: *mut LeanObject = core::ptr::null_mut();
    v_res_6030_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_6028_, v_a_6029_);
    lean_dec(v_a_6029_);
    lean_dec_ref(v_m_6028_);
    return v_res_6030_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(
    mut v___x_6031_: *mut LeanObject,
    mut v_declName_6032_: *mut LeanObject,
    mut v_as_6033_: *mut LeanObject,
    mut v_sz_6034_: usize,
    mut v_i_6035_: usize,
    mut v_b_6036_: *mut LeanObject,
    mut v___y_6037_: *mut LeanObject,
    mut v___y_6038_: *mut LeanObject,
    mut v___y_6039_: *mut LeanObject,
    mut v___y_6040_: *mut LeanObject,
    mut v___y_6041_: *mut LeanObject,
    mut v___y_6042_: *mut LeanObject,
    mut v___y_6043_: *mut LeanObject,
    mut v___y_6044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6046_: u8 = 0;
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: u8 = 0;
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: usize = 0;
    let mut v___x_6059_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6046_ = lean_usize_dec_lt(v_i_6035_, v_sz_6034_);
                if v___x_6046_ == 0 {
                    lean_dec(v_declName_6032_);
                    v___x_6047_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6047_, 0, v_b_6036_);
                    return v___x_6047_;
                } else {
                    v___x_6048_ = l_Lean_Environment_header(v___x_6031_);
                    v_modules_6049_ = lean_ctor_get(v___x_6048_, 3);
                    lean_inc_ref(v_modules_6049_);
                    lean_dec_ref(v___x_6048_);
                    v___x_6050_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_6051_ = lean_array_uget_borrowed(v_as_6033_, v_i_6035_);
                    v___x_6052_ = lean_array_get(v___x_6050_, v_modules_6049_, v_a_6051_);
                    lean_dec_ref(v_modules_6049_);
                    v_toImport_6053_ = lean_ctor_get(v___x_6052_, 0);
                    lean_inc_ref(v_toImport_6053_);
                    lean_dec(v___x_6052_);
                    v_module_6054_ = lean_ctor_get(v_toImport_6053_, 0);
                    lean_inc(v_module_6054_);
                    lean_dec_ref(v_toImport_6053_);
                    v___x_6055_ = 0;
                    lean_inc(v_declName_6032_);
                    v___x_6056_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_6054_, v___x_6055_, v_declName_6032_, v___y_6037_, v___y_6038_, v___y_6039_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_, v___y_6044_);
                    if lean_obj_tag(v___x_6056_) == 0 {
                        lean_dec_ref_known(v___x_6056_, 1);
                        v___x_6057_ = lean_box(0);
                        v___x_6058_ = 1usize;
                        v___x_6059_ = lean_usize_add(v_i_6035_, v___x_6058_);
                        v_i_6035_ = v___x_6059_;
                        v_b_6036_ = v___x_6057_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declName_6032_);
                        return v___x_6056_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6___boxed(
    mut v___x_6061_: *mut LeanObject,
    mut v_declName_6062_: *mut LeanObject,
    mut v_as_6063_: *mut LeanObject,
    mut v_sz_6064_: *mut LeanObject,
    mut v_i_6065_: *mut LeanObject,
    mut v_b_6066_: *mut LeanObject,
    mut v___y_6067_: *mut LeanObject,
    mut v___y_6068_: *mut LeanObject,
    mut v___y_6069_: *mut LeanObject,
    mut v___y_6070_: *mut LeanObject,
    mut v___y_6071_: *mut LeanObject,
    mut v___y_6072_: *mut LeanObject,
    mut v___y_6073_: *mut LeanObject,
    mut v___y_6074_: *mut LeanObject,
    mut v___y_6075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6076_: usize = 0;
    let mut v_i_boxed_6077_: usize = 0;
    let mut v_res_6078_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6076_ = lean_unbox_usize(v_sz_6064_);
    lean_dec(v_sz_6064_);
    v_i_boxed_6077_ = lean_unbox_usize(v_i_6065_);
    lean_dec(v_i_6065_);
    v_res_6078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v___x_6061_, v_declName_6062_, v_as_6063_, v_sz_boxed_6076_, v_i_boxed_6077_, v_b_6066_, v___y_6067_, v___y_6068_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_);
    lean_dec(v___y_6074_);
    lean_dec_ref(v___y_6073_);
    lean_dec(v___y_6072_);
    lean_dec_ref(v___y_6071_);
    lean_dec(v___y_6070_);
    lean_dec_ref(v___y_6069_);
    lean_dec(v___y_6068_);
    lean_dec_ref(v___y_6067_);
    lean_dec_ref(v_as_6063_);
    lean_dec_ref(v___x_6061_);
    return v_res_6078_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2()
-> *mut LeanObject {
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    v___x_6081_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1;
    v___x_6082_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0;
    v___x_6083_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_6082_, v___x_6081_);
    return v___x_6083_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(
    mut v_declName_6086_: *mut LeanObject,
    mut v_isMeta_6087_: u8,
    mut v___y_6088_: *mut LeanObject,
    mut v___y_6089_: *mut LeanObject,
    mut v___y_6090_: *mut LeanObject,
    mut v___y_6091_: *mut LeanObject,
    mut v___y_6092_: *mut LeanObject,
    mut v___y_6093_: *mut LeanObject,
    mut v___y_6094_: *mut LeanObject,
    mut v___y_6095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6105_: usize = 0;
    let mut v___x_6106_: usize = 0;
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6110_: u8 = 0;
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6114_: u8 = 0;
    let mut v_unused_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: u8 = 0;
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6127_: u8 = 0;
    let mut v_toImport_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: u8 = 0;
    let mut v___x_6139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6097_ = lean_st_ref_get(v___y_6095_);
                v_env_6101_ = lean_ctor_get(v___x_6097_, 0);
                lean_inc_ref(v_env_6101_);
                lean_dec(v___x_6097_);
                v___x_6116_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6101_, v_declName_6086_);
                if lean_obj_tag(v___x_6116_) == 0 {
                    lean_dec_ref(v_env_6101_);
                    lean_dec(v_declName_6086_);
                    state = 1;
                    continue;
                } else {
                    v_val_6117_ = lean_ctor_get(v___x_6116_, 0);
                    lean_inc(v_val_6117_);
                    lean_dec_ref_known(v___x_6116_, 1);
                    v___x_6118_ = l_Lean_Environment_header(v_env_6101_);
                    v_modules_6119_ = lean_ctor_get(v___x_6118_, 3);
                    lean_inc_ref(v_modules_6119_);
                    lean_dec_ref(v___x_6118_);
                    v___x_6120_ = lean_array_get_size(v_modules_6119_);
                    v___x_6121_ = lean_nat_dec_lt(v_val_6117_, v___x_6120_);
                    if v___x_6121_ == 0 {
                        lean_dec_ref(v_modules_6119_);
                        lean_dec(v_val_6117_);
                        lean_dec_ref(v_env_6101_);
                        lean_dec(v_declName_6086_);
                        state = 1;
                        continue;
                    } else {
                        v___x_6122_ = lean_st_ref_get(v___y_6095_);
                        v_env_6123_ = lean_ctor_get(v___x_6122_, 0);
                        lean_inc_ref(v_env_6123_);
                        lean_dec(v___x_6122_);
                        v___x_6124_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2);
                        v___x_6125_ = lean_array_fget(v_modules_6119_, v_val_6117_);
                        lean_dec(v_val_6117_);
                        lean_dec_ref(v_modules_6119_);
                        if v_isMeta_6087_ == 0 {
                            lean_dec_ref(v_env_6123_);
                            v___y_6127_ = v_isMeta_6087_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_declName_6086_);
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
                v___x_6099_ = lean_box(0);
                v___x_6100_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6100_, 0, v___x_6099_);
                return v___x_6100_;
            }
            2 => {
                v___x_6104_ = lean_box(0);
                v_sz_6105_ = lean_array_size(v___y_6103_);
                v___x_6106_ = 0usize;
                v___x_6107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v_env_6101_, v_declName_6086_, v___y_6103_, v_sz_6105_, v___x_6106_, v___x_6104_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_);
                lean_dec_ref(v___y_6103_);
                lean_dec_ref(v_env_6101_);
                if lean_obj_tag(v___x_6107_) == 0 {
                    v_isSharedCheck_6114_ = (!lean_is_exclusive(v___x_6107_)) as u8;
                    if v_isSharedCheck_6114_ == 0 {
                        v_unused_6115_ = lean_ctor_get(v___x_6107_, 0);
                        lean_dec(v_unused_6115_);
                        v___x_6109_ = v___x_6107_;
                        v_isShared_6110_ = v_isSharedCheck_6114_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_6107_);
                        v___x_6109_ = lean_box(0);
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
                    lean_ctor_set(v___x_6109_, 0, v___x_6104_);
                    v___x_6112_ = v___x_6109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6113_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6113_, 0, v___x_6104_);
                    v___x_6112_ = v_reuseFailAlloc_6113_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6112_;
            }
            5 => {
                v_toImport_6128_ = lean_ctor_get(v___x_6125_, 0);
                lean_inc_ref(v_toImport_6128_);
                lean_dec(v___x_6125_);
                v_module_6129_ = lean_ctor_get(v_toImport_6128_, 0);
                lean_inc(v_module_6129_);
                lean_dec_ref(v_toImport_6128_);
                lean_inc(v_declName_6086_);
                v___x_6130_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_6129_, v___y_6127_, v_declName_6086_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_);
                if lean_obj_tag(v___x_6130_) == 0 {
                    lean_dec_ref_known(v___x_6130_, 1);
                    v___x_6131_ = l_Lean_indirectModUseExt;
                    v___x_6132_ = lean_box(1);
                    v___x_6133_ = lean_box(0);
                    lean_inc_ref(v_env_6101_);
                    v___x_6134_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_6124_,
                        v___x_6131_,
                        v_env_6101_,
                        v___x_6132_,
                        v___x_6133_,
                    );
                    v___x_6135_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v___x_6134_, v_declName_6086_);
                    lean_dec(v___x_6134_);
                    if lean_obj_tag(v___x_6135_) == 0 {
                        v___x_6136_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3;
                        v___y_6103_ = v___x_6136_;
                        state = 2;
                        continue;
                    } else {
                        v_val_6137_ = lean_ctor_get(v___x_6135_, 0);
                        lean_inc(v_val_6137_);
                        lean_dec_ref_known(v___x_6135_, 1);
                        v___y_6103_ = v_val_6137_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_6101_);
                    lean_dec(v_declName_6086_);
                    return v___x_6130_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(
    mut v_declName_6140_: *mut LeanObject,
    mut v_isMeta_6141_: *mut LeanObject,
    mut v___y_6142_: *mut LeanObject,
    mut v___y_6143_: *mut LeanObject,
    mut v___y_6144_: *mut LeanObject,
    mut v___y_6145_: *mut LeanObject,
    mut v___y_6146_: *mut LeanObject,
    mut v___y_6147_: *mut LeanObject,
    mut v___y_6148_: *mut LeanObject,
    mut v___y_6149_: *mut LeanObject,
    mut v___y_6150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_6151_: u8 = 0;
    let mut v_res_6152_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_6151_ = (lean_unbox(v_isMeta_6141_) as u8);
    v_res_6152_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_declName_6140_, v_isMeta_boxed_6151_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_);
    lean_dec(v___y_6149_);
    lean_dec_ref(v___y_6148_);
    lean_dec(v___y_6147_);
    lean_dec_ref(v___y_6146_);
    lean_dec(v___y_6145_);
    lean_dec_ref(v___y_6144_);
    lean_dec(v___y_6143_);
    lean_dec_ref(v___y_6142_);
    return v_res_6152_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(
    mut v_as_x27_6153_: *mut LeanObject,
    mut v_b_6154_: *mut LeanObject,
    mut v___y_6155_: *mut LeanObject,
    mut v___y_6156_: *mut LeanObject,
    mut v___y_6157_: *mut LeanObject,
    mut v___y_6158_: *mut LeanObject,
    mut v___y_6159_: *mut LeanObject,
    mut v___y_6160_: *mut LeanObject,
    mut v___y_6161_: *mut LeanObject,
    mut v___y_6162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: u8 = 0;
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_6153_) == 0 {
                    v___x_6164_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6164_, 0, v_b_6154_);
                    return v___x_6164_;
                } else {
                    v_head_6165_ = lean_ctor_get(v_as_x27_6153_, 0);
                    v_tail_6166_ = lean_ctor_get(v_as_x27_6153_, 1);
                    v___x_6167_ = 1;
                    lean_inc(v_head_6165_);
                    v___x_6168_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_head_6165_, v___x_6167_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_);
                    if lean_obj_tag(v___x_6168_) == 0 {
                        lean_dec_ref_known(v___x_6168_, 1);
                        v___x_6169_ = lean_box(0);
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
    mut v_as_x27_6171_: *mut LeanObject,
    mut v_b_6172_: *mut LeanObject,
    mut v___y_6173_: *mut LeanObject,
    mut v___y_6174_: *mut LeanObject,
    mut v___y_6175_: *mut LeanObject,
    mut v___y_6176_: *mut LeanObject,
    mut v___y_6177_: *mut LeanObject,
    mut v___y_6178_: *mut LeanObject,
    mut v___y_6179_: *mut LeanObject,
    mut v___y_6180_: *mut LeanObject,
    mut v___y_6181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6182_: *mut LeanObject = core::ptr::null_mut();
    v_res_6182_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_6171_, v_b_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_);
    lean_dec(v___y_6180_);
    lean_dec_ref(v___y_6179_);
    lean_dec(v___y_6178_);
    lean_dec_ref(v___y_6177_);
    lean_dec(v___y_6176_);
    lean_dec_ref(v___y_6175_);
    lean_dec(v___y_6174_);
    lean_dec_ref(v___y_6173_);
    lean_dec(v_as_x27_6171_);
    return v_res_6182_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(
    mut v_env_6183_: *mut LeanObject,
    mut v_declName_6184_: *mut LeanObject,
    mut v___y_6185_: *mut LeanObject,
    mut v___y_6186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6187_: u8 = 0;
    let mut v_env_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: u8 = 0;
    let mut v___x_6191_: u8 = 0;
    v___x_6187_ = 0;
    v_env_6188_ = l_Lean_Environment_setExporting(v_env_6183_, v___x_6187_);
    lean_inc(v_declName_6184_);
    v___x_6189_ = l_Lean_mkPrivateName(v_env_6188_, v_declName_6184_);
    v___x_6190_ = 1;
    lean_inc_ref(v_env_6188_);
    v___x_6191_ = l_Lean_Environment_contains(v_env_6188_, v___x_6189_, v___x_6190_);
    if v___x_6191_ == 0 {
        let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6193_: u8 = 0;
        let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
        v___x_6192_ = l_Lean_privateToUserName(v_declName_6184_);
        v___x_6193_ = l_Lean_Environment_contains(v_env_6188_, v___x_6192_, v___x_6190_);
        v___x_6194_ = lean_box((v___x_6193_) as usize);
        v___x_6195_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_6195_, 0, v___x_6194_);
        lean_ctor_set(v___x_6195_, 1, v___y_6186_);
        return v___x_6195_;
    } else {
        let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6197_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_env_6188_);
        lean_dec(v_declName_6184_);
        v___x_6196_ = lean_box((v___x_6191_) as usize);
        v___x_6197_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_6197_, 0, v___x_6196_);
        lean_ctor_set(v___x_6197_, 1, v___y_6186_);
        return v___x_6197_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed(
    mut v_env_6198_: *mut LeanObject,
    mut v_declName_6199_: *mut LeanObject,
    mut v___y_6200_: *mut LeanObject,
    mut v___y_6201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6202_: *mut LeanObject = core::ptr::null_mut();
    v_res_6202_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(v_env_6198_, v_declName_6199_, v___y_6200_, v___y_6201_);
    lean_dec_ref(v___y_6200_);
    return v_res_6202_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(
    mut v_x_6204_: *mut LeanObject,
    mut v___y_6205_: *mut LeanObject,
    mut v___y_6206_: *mut LeanObject,
    mut v___y_6207_: *mut LeanObject,
    mut v___y_6208_: *mut LeanObject,
    mut v___y_6209_: *mut LeanObject,
    mut v___y_6210_: *mut LeanObject,
    mut v___y_6211_: *mut LeanObject,
    mut v___y_6212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_methods_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroScope_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6254_: u8 = 0;
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6262_: u8 = 0;
    let mut v___x_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6266_: u8 = 0;
    let mut v_unused_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6271_: u8 = 0;
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6275_: u8 = 0;
    let mut v_reuseFailAlloc_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6277_: u8 = 0;
    let mut v_unused_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6282_: u8 = 0;
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6286_: u8 = 0;
    let mut v_a_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: u8 = 0;
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6214_ = lean_st_ref_get(v___y_6212_);
                v_env_6215_ = lean_ctor_get(v___x_6214_, 0);
                lean_inc_ref_n(v_env_6215_, 4);
                lean_dec(v___x_6214_);
                v_options_6216_ = lean_ctor_get(v___y_6211_, 2);
                v_currRecDepth_6217_ = lean_ctor_get(v___y_6211_, 3);
                v_maxRecDepth_6218_ = lean_ctor_get(v___y_6211_, 4);
                v_ref_6219_ = lean_ctor_get(v___y_6211_, 5);
                v_currNamespace_6220_ = lean_ctor_get(v___y_6211_, 6);
                v_openDecls_6221_ = lean_ctor_get(v___y_6211_, 7);
                v_quotContext_6222_ = lean_ctor_get(v___y_6211_, 10);
                v_currMacroScope_6223_ = lean_ctor_get(v___y_6211_, 11);
                v___x_6224_ = lean_st_ref_get(v___y_6212_);
                v_nextMacroScope_6225_ = lean_ctor_get(v___x_6224_, 1);
                lean_inc(v_nextMacroScope_6225_);
                lean_dec(v___x_6224_);
                v___f_6226_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                lean_closure_set(v___f_6226_, 0, v_env_6215_);
                v___f_6227_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                lean_closure_set(v___f_6227_, 0, v_env_6215_);
                lean_inc_n(v_openDecls_6221_, 2);
                lean_inc_n(v_currNamespace_6220_, 3);
                v___f_6228_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___f_6228_, 0, v_env_6215_);
                lean_closure_set(v___f_6228_, 1, v_currNamespace_6220_);
                lean_closure_set(v___f_6228_, 2, v_openDecls_6221_);
                v___f_6229_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_6229_, 0, v_currNamespace_6220_);
                lean_inc_ref(v_options_6216_);
                v___f_6230_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                lean_closure_set(v___f_6230_, 0, v_env_6215_);
                lean_closure_set(v___f_6230_, 1, v_options_6216_);
                lean_closure_set(v___f_6230_, 2, v_currNamespace_6220_);
                lean_closure_set(v___f_6230_, 3, v_openDecls_6221_);
                v_methods_6231_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v_methods_6231_, 0, v___f_6226_);
                lean_ctor_set(v_methods_6231_, 1, v___f_6229_);
                lean_ctor_set(v_methods_6231_, 2, v___f_6227_);
                lean_ctor_set(v_methods_6231_, 3, v___f_6228_);
                lean_ctor_set(v_methods_6231_, 4, v___f_6230_);
                lean_inc(v_ref_6219_);
                lean_inc(v_maxRecDepth_6218_);
                lean_inc(v_currRecDepth_6217_);
                lean_inc(v_currMacroScope_6223_);
                lean_inc(v_quotContext_6222_);
                v___x_6232_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_6232_, 0, v_methods_6231_);
                lean_ctor_set(v___x_6232_, 1, v_quotContext_6222_);
                lean_ctor_set(v___x_6232_, 2, v_currMacroScope_6223_);
                lean_ctor_set(v___x_6232_, 3, v_currRecDepth_6217_);
                lean_ctor_set(v___x_6232_, 4, v_maxRecDepth_6218_);
                lean_ctor_set(v___x_6232_, 5, v_ref_6219_);
                v___x_6233_ = lean_box(0);
                v___x_6234_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_6234_, 0, v_nextMacroScope_6225_);
                lean_ctor_set(v___x_6234_, 1, v___x_6233_);
                lean_ctor_set(v___x_6234_, 2, v___x_6233_);
                v___x_6235_ = lean_apply_2(v_x_6204_, v___x_6232_, v___x_6234_);
                if lean_obj_tag(v___x_6235_) == 0 {
                    v_a_6236_ = lean_ctor_get(v___x_6235_, 1);
                    lean_inc(v_a_6236_);
                    v_a_6237_ = lean_ctor_get(v___x_6235_, 0);
                    lean_inc(v_a_6237_);
                    lean_dec_ref_known(v___x_6235_, 2);
                    v_macroScope_6238_ = lean_ctor_get(v_a_6236_, 0);
                    lean_inc(v_macroScope_6238_);
                    v_traceMsgs_6239_ = lean_ctor_get(v_a_6236_, 1);
                    lean_inc(v_traceMsgs_6239_);
                    v_expandedMacroDecls_6240_ = lean_ctor_get(v_a_6236_, 2);
                    lean_inc(v_expandedMacroDecls_6240_);
                    lean_dec(v_a_6236_);
                    v___x_6241_ = lean_box(0);
                    v___x_6242_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_expandedMacroDecls_6240_, v___x_6241_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_);
                    lean_dec(v_expandedMacroDecls_6240_);
                    if lean_obj_tag(v___x_6242_) == 0 {
                        lean_dec_ref_known(v___x_6242_, 1);
                        v___x_6243_ = lean_st_ref_take(v___y_6212_);
                        v_env_6244_ = lean_ctor_get(v___x_6243_, 0);
                        v_ngen_6245_ = lean_ctor_get(v___x_6243_, 2);
                        v_auxDeclNGen_6246_ = lean_ctor_get(v___x_6243_, 3);
                        v_traceState_6247_ = lean_ctor_get(v___x_6243_, 4);
                        v_cache_6248_ = lean_ctor_get(v___x_6243_, 5);
                        v_messages_6249_ = lean_ctor_get(v___x_6243_, 6);
                        v_infoState_6250_ = lean_ctor_get(v___x_6243_, 7);
                        v_snapshotTasks_6251_ = lean_ctor_get(v___x_6243_, 8);
                        v_isSharedCheck_6277_ = (!lean_is_exclusive(v___x_6243_)) as u8;
                        if v_isSharedCheck_6277_ == 0 {
                            v_unused_6278_ = lean_ctor_get(v___x_6243_, 1);
                            lean_dec(v_unused_6278_);
                            v___x_6253_ = v___x_6243_;
                            v_isShared_6254_ = v_isSharedCheck_6277_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_6251_);
                            lean_inc(v_infoState_6250_);
                            lean_inc(v_messages_6249_);
                            lean_inc(v_cache_6248_);
                            lean_inc(v_traceState_6247_);
                            lean_inc(v_auxDeclNGen_6246_);
                            lean_inc(v_ngen_6245_);
                            lean_inc(v_env_6244_);
                            lean_dec(v___x_6243_);
                            v___x_6253_ = lean_box(0);
                            v_isShared_6254_ = v_isSharedCheck_6277_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_traceMsgs_6239_);
                        lean_dec(v_macroScope_6238_);
                        lean_dec(v_a_6237_);
                        v_a_6279_ = lean_ctor_get(v___x_6242_, 0);
                        v_isSharedCheck_6286_ = (!lean_is_exclusive(v___x_6242_)) as u8;
                        if v_isSharedCheck_6286_ == 0 {
                            v___x_6281_ = v___x_6242_;
                            v_isShared_6282_ = v_isSharedCheck_6286_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6279_);
                            lean_dec(v___x_6242_);
                            v___x_6281_ = lean_box(0);
                            v_isShared_6282_ = v_isSharedCheck_6286_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_6287_ = lean_ctor_get(v___x_6235_, 0);
                    lean_inc(v_a_6287_);
                    lean_dec_ref_known(v___x_6235_, 2);
                    if lean_obj_tag(v_a_6287_) == 0 {
                        v_a_6288_ = lean_ctor_get(v_a_6287_, 0);
                        lean_inc(v_a_6288_);
                        v_a_6289_ = lean_ctor_get(v_a_6287_, 1);
                        lean_inc_ref(v_a_6289_);
                        lean_dec_ref_known(v_a_6287_, 2);
                        v___x_6290_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0;
                        v___x_6291_ = lean_string_dec_eq(v_a_6289_, v___x_6290_);
                        if v___x_6291_ == 0 {
                            v___x_6292_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_6292_, 0, v_a_6289_);
                            v___x_6293_ = l_Lean_MessageData_ofFormat(v___x_6292_);
                            v___x_6294_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_a_6288_, v___x_6293_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_);
                            lean_dec(v_a_6288_);
                            return v___x_6294_;
                        } else {
                            lean_dec_ref(v_a_6289_);
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
                    lean_ctor_set(v___x_6253_, 1, v_macroScope_6238_);
                    v___x_6256_ = v___x_6253_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6276_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6276_, 0, v_env_6244_);
                    lean_ctor_set(v_reuseFailAlloc_6276_, 1, v_macroScope_6238_);
                    lean_ctor_set(v_reuseFailAlloc_6276_, 2, v_ngen_6245_);
                    lean_ctor_set(v_reuseFailAlloc_6276_, 3, v_auxDeclNGen_6246_);
                    lean_ctor_set(v_reuseFailAlloc_6276_, 4, v_traceState_6247_);
                    lean_ctor_set(v_reuseFailAlloc_6276_, 5, v_cache_6248_);
                    lean_ctor_set(v_reuseFailAlloc_6276_, 6, v_messages_6249_);
                    lean_ctor_set(v_reuseFailAlloc_6276_, 7, v_infoState_6250_);
                    lean_ctor_set(v_reuseFailAlloc_6276_, 8, v_snapshotTasks_6251_);
                    v___x_6256_ = v_reuseFailAlloc_6276_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6257_ = lean_st_ref_set(v___y_6212_, v___x_6256_);
                v___x_6258_ = l_List_reverse___redArg(v_traceMsgs_6239_);
                v___x_6259_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v___x_6258_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_);
                if lean_obj_tag(v___x_6259_) == 0 {
                    v_isSharedCheck_6266_ = (!lean_is_exclusive(v___x_6259_)) as u8;
                    if v_isSharedCheck_6266_ == 0 {
                        v_unused_6267_ = lean_ctor_get(v___x_6259_, 0);
                        lean_dec(v_unused_6267_);
                        v___x_6261_ = v___x_6259_;
                        v_isShared_6262_ = v_isSharedCheck_6266_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_6259_);
                        v___x_6261_ = lean_box(0);
                        v_isShared_6262_ = v_isSharedCheck_6266_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6237_);
                    v_a_6268_ = lean_ctor_get(v___x_6259_, 0);
                    v_isSharedCheck_6275_ = (!lean_is_exclusive(v___x_6259_)) as u8;
                    if v_isSharedCheck_6275_ == 0 {
                        v___x_6270_ = v___x_6259_;
                        v_isShared_6271_ = v_isSharedCheck_6275_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6268_);
                        lean_dec(v___x_6259_);
                        v___x_6270_ = lean_box(0);
                        v_isShared_6271_ = v_isSharedCheck_6275_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6262_ == 0 {
                    lean_ctor_set(v___x_6261_, 0, v_a_6237_);
                    v___x_6264_ = v___x_6261_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6265_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6265_, 0, v_a_6237_);
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
                    v_reuseFailAlloc_6274_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6274_, 0, v_a_6268_);
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
                    v_reuseFailAlloc_6285_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6285_, 0, v_a_6279_);
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
    mut v_x_6297_: *mut LeanObject,
    mut v___y_6298_: *mut LeanObject,
    mut v___y_6299_: *mut LeanObject,
    mut v___y_6300_: *mut LeanObject,
    mut v___y_6301_: *mut LeanObject,
    mut v___y_6302_: *mut LeanObject,
    mut v___y_6303_: *mut LeanObject,
    mut v___y_6304_: *mut LeanObject,
    mut v___y_6305_: *mut LeanObject,
    mut v___y_6306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6307_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6305_);
    lean_dec_ref(v___y_6304_);
    lean_dec(v___y_6303_);
    lean_dec_ref(v___y_6302_);
    lean_dec(v___y_6301_);
    lean_dec_ref(v___y_6300_);
    lean_dec(v___y_6299_);
    lean_dec_ref(v___y_6298_);
    return v_res_6307_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(
    mut v_x_6318_: *mut LeanObject,
    mut v_a_6319_: *mut LeanObject,
    mut v_a_6320_: *mut LeanObject,
    mut v_a_6321_: *mut LeanObject,
    mut v_a_6322_: *mut LeanObject,
    mut v_a_6323_: *mut LeanObject,
    mut v_a_6324_: *mut LeanObject,
    mut v_a_6325_: *mut LeanObject,
    mut v_a_6326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: u8 = 0;
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyp_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: u8 = 0;
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pat_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6350_: u8 = 0;
    let mut v___x_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6354_: u8 = 0;
    let mut v_a_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6358_: u8 = 0;
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6328_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2;
                lean_inc(v_x_6318_);
                v___x_6329_ = l_Lean_Syntax_isOfKind(v_x_6318_, v___x_6328_);
                if v___x_6329_ == 0 {
                    lean_dec(v_x_6318_);
                    v___x_6330_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
                    return v___x_6330_;
                } else {
                    v___x_6331_ = lean_unsigned_to_nat(1);
                    v_hyp_6332_ = l_Lean_Syntax_getArg(v_x_6318_, v___x_6331_);
                    v___x_6333_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4;
                    lean_inc(v_hyp_6332_);
                    v___x_6334_ = l_Lean_Syntax_isOfKind(v_hyp_6332_, v___x_6333_);
                    if v___x_6334_ == 0 {
                        lean_dec(v_hyp_6332_);
                        lean_dec(v_x_6318_);
                        v___x_6335_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
                        return v___x_6335_;
                    } else {
                        v___x_6336_ = lean_unsigned_to_nat(3);
                        v_pat_6337_ = l_Lean_Syntax_getArg(v_x_6318_, v___x_6336_);
                        lean_dec(v_x_6318_);
                        v___x_6338_ = lean_alloc_closure(
                            l_Lean_Parser_Tactic_MCasesPat_parse___boxed as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        lean_closure_set(v___x_6338_, 0, v_pat_6337_);
                        v___x_6339_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v___x_6338_, v_a_6319_, v_a_6320_, v_a_6321_, v_a_6322_, v_a_6323_, v_a_6324_, v_a_6325_, v_a_6326_);
                        if lean_obj_tag(v___x_6339_) == 0 {
                            v_a_6340_ = lean_ctor_get(v___x_6339_, 0);
                            lean_inc(v_a_6340_);
                            lean_dec_ref_known(v___x_6339_, 1);
                            v___x_6341_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                                v_a_6320_, v_a_6323_, v_a_6324_, v_a_6325_, v_a_6326_,
                            );
                            if lean_obj_tag(v___x_6341_) == 0 {
                                v_a_6342_ = lean_ctor_get(v___x_6341_, 0);
                                lean_inc(v_a_6342_);
                                lean_dec_ref_known(v___x_6341_, 1);
                                v_fst_6343_ = lean_ctor_get(v_a_6342_, 0);
                                lean_inc_n(v_fst_6343_, 2);
                                v_snd_6344_ = lean_ctor_get(v_a_6342_, 1);
                                lean_inc(v_snd_6344_);
                                lean_dec(v_a_6342_);
                                v___f_6345_ = lean_alloc_closure(
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    13,
                                    4,
                                );
                                lean_closure_set(v___f_6345_, 0, v_snd_6344_);
                                lean_closure_set(v___f_6345_, 1, v_hyp_6332_);
                                lean_closure_set(v___f_6345_, 2, v_a_6340_);
                                lean_closure_set(v___f_6345_, 3, v_fst_6343_);
                                v___x_6346_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_fst_6343_, v___f_6345_, v_a_6319_, v_a_6320_, v_a_6321_, v_a_6322_, v_a_6323_, v_a_6324_, v_a_6325_, v_a_6326_);
                                return v___x_6346_;
                            } else {
                                lean_dec(v_a_6340_);
                                lean_dec(v_hyp_6332_);
                                v_a_6347_ = lean_ctor_get(v___x_6341_, 0);
                                v_isSharedCheck_6354_ = (!lean_is_exclusive(v___x_6341_)) as u8;
                                if v_isSharedCheck_6354_ == 0 {
                                    v___x_6349_ = v___x_6341_;
                                    v_isShared_6350_ = v_isSharedCheck_6354_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_6347_);
                                    lean_dec(v___x_6341_);
                                    v___x_6349_ = lean_box(0);
                                    v_isShared_6350_ = v_isSharedCheck_6354_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_hyp_6332_);
                            v_a_6355_ = lean_ctor_get(v___x_6339_, 0);
                            v_isSharedCheck_6362_ = (!lean_is_exclusive(v___x_6339_)) as u8;
                            if v_isSharedCheck_6362_ == 0 {
                                v___x_6357_ = v___x_6339_;
                                v_isShared_6358_ = v_isSharedCheck_6362_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_6355_);
                                lean_dec(v___x_6339_);
                                v___x_6357_ = lean_box(0);
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
                    v_reuseFailAlloc_6353_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6353_, 0, v_a_6347_);
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
                    v_reuseFailAlloc_6361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6361_, 0, v_a_6355_);
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
    mut v_x_6363_: *mut LeanObject,
    mut v_a_6364_: *mut LeanObject,
    mut v_a_6365_: *mut LeanObject,
    mut v_a_6366_: *mut LeanObject,
    mut v_a_6367_: *mut LeanObject,
    mut v_a_6368_: *mut LeanObject,
    mut v_a_6369_: *mut LeanObject,
    mut v_a_6370_: *mut LeanObject,
    mut v_a_6371_: *mut LeanObject,
    mut v_a_6372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6373_: *mut LeanObject = core::ptr::null_mut();
    v_res_6373_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(
        v_x_6363_, v_a_6364_, v_a_6365_, v_a_6366_, v_a_6367_, v_a_6368_, v_a_6369_, v_a_6370_,
        v_a_6371_,
    );
    lean_dec(v_a_6371_);
    lean_dec_ref(v_a_6370_);
    lean_dec(v_a_6369_);
    lean_dec_ref(v_a_6368_);
    lean_dec(v_a_6367_);
    lean_dec_ref(v_a_6366_);
    lean_dec(v_a_6365_);
    lean_dec_ref(v_a_6364_);
    return v_res_6373_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(
    mut v_00_u03b1_6374_: *mut LeanObject,
    mut v_x_6375_: *mut LeanObject,
    mut v___y_6376_: *mut LeanObject,
    mut v___y_6377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    v___x_6378_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_6375_, v___y_6377_);
    return v___x_6378_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___boxed(
    mut v_00_u03b1_6379_: *mut LeanObject,
    mut v_x_6380_: *mut LeanObject,
    mut v___y_6381_: *mut LeanObject,
    mut v___y_6382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6383_: *mut LeanObject = core::ptr::null_mut();
    v_res_6383_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(v_00_u03b1_6379_, v_x_6380_, v___y_6381_, v___y_6382_);
    lean_dec_ref(v___y_6381_);
    lean_dec_ref(v_x_6380_);
    return v_res_6383_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(
    mut v_00_u03b1_6384_: *mut LeanObject,
    mut v_ref_6385_: *mut LeanObject,
    mut v___y_6386_: *mut LeanObject,
    mut v___y_6387_: *mut LeanObject,
    mut v___y_6388_: *mut LeanObject,
    mut v___y_6389_: *mut LeanObject,
    mut v___y_6390_: *mut LeanObject,
    mut v___y_6391_: *mut LeanObject,
    mut v___y_6392_: *mut LeanObject,
    mut v___y_6393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    v___x_6395_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_6385_);
    return v___x_6395_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___boxed(
    mut v_00_u03b1_6396_: *mut LeanObject,
    mut v_ref_6397_: *mut LeanObject,
    mut v___y_6398_: *mut LeanObject,
    mut v___y_6399_: *mut LeanObject,
    mut v___y_6400_: *mut LeanObject,
    mut v___y_6401_: *mut LeanObject,
    mut v___y_6402_: *mut LeanObject,
    mut v___y_6403_: *mut LeanObject,
    mut v___y_6404_: *mut LeanObject,
    mut v___y_6405_: *mut LeanObject,
    mut v___y_6406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6407_: *mut LeanObject = core::ptr::null_mut();
    v_res_6407_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(v_00_u03b1_6396_, v_ref_6397_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_, v___y_6403_, v___y_6404_, v___y_6405_);
    lean_dec(v___y_6405_);
    lean_dec_ref(v___y_6404_);
    lean_dec(v___y_6403_);
    lean_dec_ref(v___y_6402_);
    lean_dec(v___y_6401_);
    lean_dec_ref(v___y_6400_);
    lean_dec(v___y_6399_);
    lean_dec_ref(v___y_6398_);
    return v_res_6407_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(
    mut v_00_u03b1_6408_: *mut LeanObject,
    mut v_x_6409_: *mut LeanObject,
    mut v___y_6410_: *mut LeanObject,
    mut v___y_6411_: *mut LeanObject,
    mut v___y_6412_: *mut LeanObject,
    mut v___y_6413_: *mut LeanObject,
    mut v___y_6414_: *mut LeanObject,
    mut v___y_6415_: *mut LeanObject,
    mut v___y_6416_: *mut LeanObject,
    mut v___y_6417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6420_: *mut LeanObject,
    mut v_x_6421_: *mut LeanObject,
    mut v___y_6422_: *mut LeanObject,
    mut v___y_6423_: *mut LeanObject,
    mut v___y_6424_: *mut LeanObject,
    mut v___y_6425_: *mut LeanObject,
    mut v___y_6426_: *mut LeanObject,
    mut v___y_6427_: *mut LeanObject,
    mut v___y_6428_: *mut LeanObject,
    mut v___y_6429_: *mut LeanObject,
    mut v___y_6430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6431_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6429_);
    lean_dec_ref(v___y_6428_);
    lean_dec(v___y_6427_);
    lean_dec_ref(v___y_6426_);
    lean_dec(v___y_6425_);
    lean_dec_ref(v___y_6424_);
    lean_dec(v___y_6423_);
    lean_dec_ref(v___y_6422_);
    return v_res_6431_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(
    mut v_mvarId_6432_: *mut LeanObject,
    mut v_val_6433_: *mut LeanObject,
    mut v___y_6434_: *mut LeanObject,
    mut v___y_6435_: *mut LeanObject,
    mut v___y_6436_: *mut LeanObject,
    mut v___y_6437_: *mut LeanObject,
    mut v___y_6438_: *mut LeanObject,
    mut v___y_6439_: *mut LeanObject,
    mut v___y_6440_: *mut LeanObject,
    mut v___y_6441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
    v___x_6443_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(
            v_mvarId_6432_,
            v_val_6433_,
            v___y_6439_,
        );
    return v___x_6443_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___boxed(
    mut v_mvarId_6444_: *mut LeanObject,
    mut v_val_6445_: *mut LeanObject,
    mut v___y_6446_: *mut LeanObject,
    mut v___y_6447_: *mut LeanObject,
    mut v___y_6448_: *mut LeanObject,
    mut v___y_6449_: *mut LeanObject,
    mut v___y_6450_: *mut LeanObject,
    mut v___y_6451_: *mut LeanObject,
    mut v___y_6452_: *mut LeanObject,
    mut v___y_6453_: *mut LeanObject,
    mut v___y_6454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6455_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6453_);
    lean_dec_ref(v___y_6452_);
    lean_dec(v___y_6451_);
    lean_dec_ref(v___y_6450_);
    lean_dec(v___y_6449_);
    lean_dec_ref(v___y_6448_);
    lean_dec(v___y_6447_);
    lean_dec_ref(v___y_6446_);
    return v_res_6455_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(
    mut v_cls_6456_: *mut LeanObject,
    mut v_msg_6457_: *mut LeanObject,
    mut v___y_6458_: *mut LeanObject,
    mut v___y_6459_: *mut LeanObject,
    mut v___y_6460_: *mut LeanObject,
    mut v___y_6461_: *mut LeanObject,
    mut v___y_6462_: *mut LeanObject,
    mut v___y_6463_: *mut LeanObject,
    mut v___y_6464_: *mut LeanObject,
    mut v___y_6465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6467_: *mut LeanObject = core::ptr::null_mut();
    v___x_6467_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_6456_, v_msg_6457_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_);
    return v___x_6467_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___boxed(
    mut v_cls_6468_: *mut LeanObject,
    mut v_msg_6469_: *mut LeanObject,
    mut v___y_6470_: *mut LeanObject,
    mut v___y_6471_: *mut LeanObject,
    mut v___y_6472_: *mut LeanObject,
    mut v___y_6473_: *mut LeanObject,
    mut v___y_6474_: *mut LeanObject,
    mut v___y_6475_: *mut LeanObject,
    mut v___y_6476_: *mut LeanObject,
    mut v___y_6477_: *mut LeanObject,
    mut v___y_6478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6479_: *mut LeanObject = core::ptr::null_mut();
    v_res_6479_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(v_cls_6468_, v_msg_6469_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_);
    lean_dec(v___y_6477_);
    lean_dec_ref(v___y_6476_);
    lean_dec(v___y_6475_);
    lean_dec_ref(v___y_6474_);
    lean_dec(v___y_6473_);
    lean_dec_ref(v___y_6472_);
    lean_dec(v___y_6471_);
    lean_dec_ref(v___y_6470_);
    return v_res_6479_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(
    mut v_as_6480_: *mut LeanObject,
    mut v_as_x27_6481_: *mut LeanObject,
    mut v_b_6482_: *mut LeanObject,
    mut v_a_6483_: *mut LeanObject,
    mut v___y_6484_: *mut LeanObject,
    mut v___y_6485_: *mut LeanObject,
    mut v___y_6486_: *mut LeanObject,
    mut v___y_6487_: *mut LeanObject,
    mut v___y_6488_: *mut LeanObject,
    mut v___y_6489_: *mut LeanObject,
    mut v___y_6490_: *mut LeanObject,
    mut v___y_6491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    v___x_6493_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_6481_, v_b_6482_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_);
    return v___x_6493_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___boxed(
    mut v_as_6494_: *mut LeanObject,
    mut v_as_x27_6495_: *mut LeanObject,
    mut v_b_6496_: *mut LeanObject,
    mut v_a_6497_: *mut LeanObject,
    mut v___y_6498_: *mut LeanObject,
    mut v___y_6499_: *mut LeanObject,
    mut v___y_6500_: *mut LeanObject,
    mut v___y_6501_: *mut LeanObject,
    mut v___y_6502_: *mut LeanObject,
    mut v___y_6503_: *mut LeanObject,
    mut v___y_6504_: *mut LeanObject,
    mut v___y_6505_: *mut LeanObject,
    mut v___y_6506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6507_: *mut LeanObject = core::ptr::null_mut();
    v_res_6507_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(v_as_6494_, v_as_x27_6495_, v_b_6496_, v_a_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_);
    lean_dec(v___y_6505_);
    lean_dec_ref(v___y_6504_);
    lean_dec(v___y_6503_);
    lean_dec_ref(v___y_6502_);
    lean_dec(v___y_6501_);
    lean_dec_ref(v___y_6500_);
    lean_dec(v___y_6499_);
    lean_dec_ref(v___y_6498_);
    lean_dec(v_as_x27_6495_);
    lean_dec(v_as_6494_);
    return v_res_6507_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(
    mut v_00_u03b1_6508_: *mut LeanObject,
    mut v_ref_6509_: *mut LeanObject,
    mut v_msg_6510_: *mut LeanObject,
    mut v___y_6511_: *mut LeanObject,
    mut v___y_6512_: *mut LeanObject,
    mut v___y_6513_: *mut LeanObject,
    mut v___y_6514_: *mut LeanObject,
    mut v___y_6515_: *mut LeanObject,
    mut v___y_6516_: *mut LeanObject,
    mut v___y_6517_: *mut LeanObject,
    mut v___y_6518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    v___x_6520_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_6509_, v_msg_6510_, v___y_6511_, v___y_6512_, v___y_6513_, v___y_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_);
    return v___x_6520_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___boxed(
    mut v_00_u03b1_6521_: *mut LeanObject,
    mut v_ref_6522_: *mut LeanObject,
    mut v_msg_6523_: *mut LeanObject,
    mut v___y_6524_: *mut LeanObject,
    mut v___y_6525_: *mut LeanObject,
    mut v___y_6526_: *mut LeanObject,
    mut v___y_6527_: *mut LeanObject,
    mut v___y_6528_: *mut LeanObject,
    mut v___y_6529_: *mut LeanObject,
    mut v___y_6530_: *mut LeanObject,
    mut v___y_6531_: *mut LeanObject,
    mut v___y_6532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6533_: *mut LeanObject = core::ptr::null_mut();
    v_res_6533_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(v_00_u03b1_6521_, v_ref_6522_, v_msg_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_, v___y_6529_, v___y_6530_, v___y_6531_);
    lean_dec(v___y_6531_);
    lean_dec_ref(v___y_6530_);
    lean_dec(v___y_6529_);
    lean_dec_ref(v___y_6528_);
    lean_dec(v___y_6527_);
    lean_dec_ref(v___y_6526_);
    lean_dec(v___y_6525_);
    lean_dec_ref(v___y_6524_);
    lean_dec(v_ref_6522_);
    return v_res_6533_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9(
    mut v_00_u03b2_6534_: *mut LeanObject,
    mut v_x_6535_: *mut LeanObject,
    mut v_x_6536_: *mut LeanObject,
    mut v_x_6537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    v___x_6538_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_x_6535_, v_x_6536_, v_x_6537_);
    return v___x_6538_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(
    mut v_00_u03b2_6539_: *mut LeanObject,
    mut v_m_6540_: *mut LeanObject,
    mut v_a_6541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    v___x_6542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_6540_, v_a_6541_);
    return v___x_6542_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_6543_: *mut LeanObject,
    mut v_m_6544_: *mut LeanObject,
    mut v_a_6545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6546_: *mut LeanObject = core::ptr::null_mut();
    v_res_6546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(v_00_u03b2_6543_, v_m_6544_, v_a_6545_);
    lean_dec(v_a_6545_);
    lean_dec_ref(v_m_6544_);
    return v_res_6546_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(
    mut v_00_u03b1_6547_: *mut LeanObject,
    mut v_msg_6548_: *mut LeanObject,
    mut v___y_6549_: *mut LeanObject,
    mut v___y_6550_: *mut LeanObject,
    mut v___y_6551_: *mut LeanObject,
    mut v___y_6552_: *mut LeanObject,
    mut v___y_6553_: *mut LeanObject,
    mut v___y_6554_: *mut LeanObject,
    mut v___y_6555_: *mut LeanObject,
    mut v___y_6556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
    v___x_6558_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_6548_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_);
    return v___x_6558_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___boxed(
    mut v_00_u03b1_6559_: *mut LeanObject,
    mut v_msg_6560_: *mut LeanObject,
    mut v___y_6561_: *mut LeanObject,
    mut v___y_6562_: *mut LeanObject,
    mut v___y_6563_: *mut LeanObject,
    mut v___y_6564_: *mut LeanObject,
    mut v___y_6565_: *mut LeanObject,
    mut v___y_6566_: *mut LeanObject,
    mut v___y_6567_: *mut LeanObject,
    mut v___y_6568_: *mut LeanObject,
    mut v___y_6569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6570_: *mut LeanObject = core::ptr::null_mut();
    v_res_6570_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(v_00_u03b1_6559_, v_msg_6560_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_);
    lean_dec(v___y_6568_);
    lean_dec_ref(v___y_6567_);
    lean_dec(v___y_6566_);
    lean_dec_ref(v___y_6565_);
    lean_dec(v___y_6564_);
    lean_dec_ref(v___y_6563_);
    lean_dec(v___y_6562_);
    lean_dec_ref(v___y_6561_);
    return v_res_6570_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(
    mut v_00_u03b2_6571_: *mut LeanObject,
    mut v_x_6572_: *mut LeanObject,
    mut v_x_6573_: usize,
    mut v_x_6574_: usize,
    mut v_x_6575_: *mut LeanObject,
    mut v_x_6576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    v___x_6577_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_6572_, v_x_6573_, v_x_6574_, v_x_6575_, v_x_6576_);
    return v___x_6577_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___boxed(
    mut v_00_u03b2_6578_: *mut LeanObject,
    mut v_x_6579_: *mut LeanObject,
    mut v_x_6580_: *mut LeanObject,
    mut v_x_6581_: *mut LeanObject,
    mut v_x_6582_: *mut LeanObject,
    mut v_x_6583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_22501__boxed_6584_: usize = 0;
    let mut v_x_22502__boxed_6585_: usize = 0;
    let mut v_res_6586_: *mut LeanObject = core::ptr::null_mut();
    v_x_22501__boxed_6584_ = lean_unbox_usize(v_x_6580_);
    lean_dec(v_x_6580_);
    v_x_22502__boxed_6585_ = lean_unbox_usize(v_x_6581_);
    lean_dec(v_x_6581_);
    v_res_6586_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(v_00_u03b2_6578_, v_x_6579_, v_x_22501__boxed_6584_, v_x_22502__boxed_6585_, v_x_6582_, v_x_6583_);
    return v_res_6586_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(
    mut v_00_u03b2_6587_: *mut LeanObject,
    mut v_x_6588_: *mut LeanObject,
    mut v_x_6589_: *mut LeanObject,
) -> u8 {
    let mut v___x_6590_: u8 = 0;
    v___x_6590_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_6588_, v_x_6589_);
    return v___x_6590_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___boxed(
    mut v_00_u03b2_6591_: *mut LeanObject,
    mut v_x_6592_: *mut LeanObject,
    mut v_x_6593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6594_: u8 = 0;
    let mut v_r_6595_: *mut LeanObject = core::ptr::null_mut();
    v_res_6594_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(v_00_u03b2_6591_, v_x_6592_, v_x_6593_);
    lean_dec_ref(v_x_6593_);
    lean_dec_ref(v_x_6592_);
    v_r_6595_ = lean_box((v_res_6594_) as usize);
    return v_r_6595_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(
    mut v_00_u03b2_6596_: *mut LeanObject,
    mut v_a_6597_: *mut LeanObject,
    mut v_x_6598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    v___x_6599_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_6597_, v_x_6598_);
    return v___x_6599_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___boxed(
    mut v_00_u03b2_6600_: *mut LeanObject,
    mut v_a_6601_: *mut LeanObject,
    mut v_x_6602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6603_: *mut LeanObject = core::ptr::null_mut();
    v_res_6603_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(v_00_u03b2_6600_, v_a_6601_, v_x_6602_);
    lean_dec(v_x_6602_);
    lean_dec(v_a_6601_);
    return v_res_6603_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18(
    mut v_00_u03b2_6604_: *mut LeanObject,
    mut v_n_6605_: *mut LeanObject,
    mut v_k_6606_: *mut LeanObject,
    mut v_v_6607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    v___x_6608_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v_n_6605_, v_k_6606_, v_v_6607_);
    return v___x_6608_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(
    mut v_00_u03b2_6609_: *mut LeanObject,
    mut v_depth_6610_: usize,
    mut v_keys_6611_: *mut LeanObject,
    mut v_vals_6612_: *mut LeanObject,
    mut v_heq_6613_: *mut LeanObject,
    mut v_i_6614_: *mut LeanObject,
    mut v_entries_6615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    v___x_6616_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_6610_, v_keys_6611_, v_vals_6612_, v_i_6614_, v_entries_6615_);
    return v___x_6616_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___boxed(
    mut v_00_u03b2_6617_: *mut LeanObject,
    mut v_depth_6618_: *mut LeanObject,
    mut v_keys_6619_: *mut LeanObject,
    mut v_vals_6620_: *mut LeanObject,
    mut v_heq_6621_: *mut LeanObject,
    mut v_i_6622_: *mut LeanObject,
    mut v_entries_6623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_6624_: usize = 0;
    let mut v_res_6625_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_6624_ = lean_unbox_usize(v_depth_6618_);
    lean_dec(v_depth_6618_);
    v_res_6625_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(v_00_u03b2_6617_, v_depth_boxed_6624_, v_keys_6619_, v_vals_6620_, v_heq_6621_, v_i_6622_, v_entries_6623_);
    lean_dec_ref(v_vals_6620_);
    lean_dec_ref(v_keys_6619_);
    return v_res_6625_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(
    mut v_00_u03b2_6626_: *mut LeanObject,
    mut v_x_6627_: *mut LeanObject,
    mut v_x_6628_: usize,
    mut v_x_6629_: *mut LeanObject,
) -> u8 {
    let mut v___x_6630_: u8 = 0;
    v___x_6630_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_6627_, v_x_6628_, v_x_6629_);
    return v___x_6630_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___boxed(
    mut v_00_u03b2_6631_: *mut LeanObject,
    mut v_x_6632_: *mut LeanObject,
    mut v_x_6633_: *mut LeanObject,
    mut v_x_6634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_22535__boxed_6635_: usize = 0;
    let mut v_res_6636_: u8 = 0;
    let mut v_r_6637_: *mut LeanObject = core::ptr::null_mut();
    v_x_22535__boxed_6635_ = lean_unbox_usize(v_x_6633_);
    lean_dec(v_x_6633_);
    v_res_6636_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(v_00_u03b2_6631_, v_x_6632_, v_x_22535__boxed_6635_, v_x_6634_);
    lean_dec_ref(v_x_6634_);
    lean_dec_ref(v_x_6632_);
    v_r_6637_ = lean_box((v_res_6636_) as usize);
    return v_r_6637_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20(
    mut v_00_u03b2_6638_: *mut LeanObject,
    mut v_x_6639_: *mut LeanObject,
    mut v_x_6640_: *mut LeanObject,
    mut v_x_6641_: *mut LeanObject,
    mut v_x_6642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6643_: *mut LeanObject = core::ptr::null_mut();
    v___x_6643_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_x_6639_, v_x_6640_, v_x_6641_, v_x_6642_);
    return v___x_6643_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(
    mut v_00_u03b2_6644_: *mut LeanObject,
    mut v_keys_6645_: *mut LeanObject,
    mut v_vals_6646_: *mut LeanObject,
    mut v_heq_6647_: *mut LeanObject,
    mut v_i_6648_: *mut LeanObject,
    mut v_k_6649_: *mut LeanObject,
) -> u8 {
    let mut v___x_6650_: u8 = 0;
    v___x_6650_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_6645_, v_i_6648_, v_k_6649_);
    return v___x_6650_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___boxed(
    mut v_00_u03b2_6651_: *mut LeanObject,
    mut v_keys_6652_: *mut LeanObject,
    mut v_vals_6653_: *mut LeanObject,
    mut v_heq_6654_: *mut LeanObject,
    mut v_i_6655_: *mut LeanObject,
    mut v_k_6656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6657_: u8 = 0;
    let mut v_r_6658_: *mut LeanObject = core::ptr::null_mut();
    v_res_6657_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(v_00_u03b2_6651_, v_keys_6652_, v_vals_6653_, v_heq_6654_, v_i_6655_, v_k_6656_);
    lean_dec_ref(v_k_6656_);
    lean_dec_ref(v_vals_6653_);
    lean_dec_ref(v_keys_6652_);
    v_r_6658_ = lean_box((v_res_6657_) as usize);
    return v_r_6658_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1()
-> *mut LeanObject {
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut LeanObject = core::ptr::null_mut();
    v___x_6668_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_6669_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2;
    v___x_6670_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1;
    v___x_6671_ = lean_alloc_closure(
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
    mut v_a_6673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6674_: *mut LeanObject = core::ptr::null_mut();
    v_res_6674_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
    return v_res_6674_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_Do_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
}
