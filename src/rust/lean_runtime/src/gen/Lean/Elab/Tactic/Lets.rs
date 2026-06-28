// Lean compiler output
// Module: Lean.Elab.Tactic.Lets
// Imports: Lean.Meta.Tactic.Lets Lean.Elab.Tactic.Location Lean.Elab.Binders Lean.Linter.Init Lean.Elab.ConfigEval
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_mkOptionalNode};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr6, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Binders::{
    initialize_Lean_Elab_Binders, l_Lean_Elab_Term_addLocalVarInfo,
    runtime_initialize_Lean_Elab_Binders,
};
use crate::r#gen::Lean::Elab::ConfigEval::Basic::{
    l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo,
    l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo, l_Lean_Elab_ConfigEval_ConfigItem_getRootStr,
    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous, l_Lean_Elab_ConfigEval_ConfigItem_shift,
    l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg,
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg,
    l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg,
};
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalConfigItem::l_Lean_Elab_ConfigEval_evalBoolItem;
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalExpr::l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg;
use crate::r#gen::Lean::Elab::ConfigEval::Instances::l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr;
use crate::r#gen::Lean::Elab::ConfigEval::Types::l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
use crate::r#gen::Lean::Elab::ConfigEval::{
    initialize_Lean_Elab_ConfigEval, runtime_initialize_Lean_Elab_ConfigEval,
};
use crate::r#gen::Lean::Elab::Exception::{
    l_Lean_Elab_abortTermExceptionId, l_Lean_Elab_unsupportedSyntaxExceptionId,
};
use crate::r#gen::Lean::Elab::SyntheticMVars::l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_getNameOfIdent_x27,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Location::{
    initialize_Lean_Elab_Tactic_Location, l_Lean_Elab_Tactic_expandOptLocation,
    l_Lean_Elab_Tactic_withLocation, runtime_initialize_Lean_Elab_Tactic_Location,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTermEnsuringType___boxed, l_Lean_Elab_Term_logUnassignedUsingErrorInfos,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_hasMVar, l_Lean_instInhabitedExpr, l_Lean_mkConst,
    l_Lean_mkFVar,
};
use crate::r#gen::Lean::InternalExceptionId::l_Lean_instBEqInternalExceptionId_beq;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag,
    l_Lean_Linter_linterSetsExt, runtime_initialize_Lean_Linter_Init,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add, l_Lean_indentD, l_Lean_indentExpr,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::Meta::Tactic::Lets::{
    initialize_Lean_Meta_Tactic_Lets, l_Lean_MVarId_extractLets,
    l_Lean_MVarId_extractLetsLocalDecl, l_Lean_MVarId_letToHave, l_Lean_MVarId_letToHaveLocalDecl,
    l_Lean_MVarId_liftLets, l_Lean_MVarId_liftLetsLocalDecl,
    runtime_initialize_Lean_Meta_Tactic_Lets,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Sorry::{l_Lean_Expr_hasSorry, l_Lean_Expr_hasSyntheticSorry};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_dec_lt;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_to_list,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [117, 110, 117, 115, 101, 100, 78, 97, 109, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,18255610267079397070 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,13498800986395368699 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 39, 117, 110, 117, 115, 101, 100, 32, 110, 97, 109, 101, 39, 32, 116, 97, 99, 116, 105, 99, 32, 108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,8890915805016873704 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,10249868229618157460 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,9055758596667989561 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [117, 110, 117, 115, 101, 100, 32, 110, 97, 109, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [69, 120, 116, 114, 97, 99, 116, 76, 101, 116, 115, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject,11908253882359177106 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [10, 111, 102, 32, 116, 121, 112, 101, 32, 96, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__7_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__7_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__9_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 96, 115, 111, 114, 114, 121, 96, 58, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__9_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [112, 114, 101, 115, 101, 114, 118, 101, 66, 105, 110, 100, 101, 114, 78, 97, 109, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [117, 110, 100, 101, 114, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [117, 115, 101, 67, 111, 110, 116, 101, 120, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [117, 115, 101, 100, 79, 110, 108, 121, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject,11908253882359177106 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4_value) as *mut LeanObject,14507398185897222672 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject,11908253882359177106 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3_value) as *mut LeanObject,12644480600285593555 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject,11908253882359177106 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2_value) as *mut LeanObject,436259404890627688 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 114, 111, 111, 102, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 121, 112, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject,11908253882359177106 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9_value) as *mut LeanObject,11189822338671989547 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject,11908253882359177106 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8_value) as *mut LeanObject,727219433938639063 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject,11908253882359177106 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1_value) as *mut LeanObject,12202333809195043728 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 105, 102, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 101, 114, 103, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [111, 110, 108, 121, 71, 105, 118, 101, 110, 78, 97, 109, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject,11908253882359177106 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15_value) as *mut LeanObject,2358081319198354187 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject,11908253882359177106 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14_value) as *mut LeanObject,4051472980490929722 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject,11908253882359177106 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13_value) as *mut LeanObject,14194421122204751582 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 115, 99, 101, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject,11908253882359177106 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21_value) as *mut LeanObject,10525133401186111338 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__2_value) as *mut LeanObject,11908253882359177106 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20_value) as *mut LeanObject,1082644068901154885 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0_value) as *mut LeanObject;
pub static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            39, 101, 120, 116, 114, 97, 99, 116, 95, 108, 101, 116, 115, 39, 32, 116, 97, 99, 116,
            105, 99, 32, 102, 97, 105, 108, 101, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalExtractLets___closed__0_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_evalExtractLets___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalExtractLets___closed__1_value: LeanStringObject<12> =
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
        m_data: [101, 120, 116, 114, 97, 99, 116, 76, 101, 116, 115, 0],
    };
static mut l_Lean_Elab_Tactic_evalExtractLets___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__1_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_evalExtractLets___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__1_value)
                as *mut LeanObject,
            14570852858352645221 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalExtractLets___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalExtractLets___closed__3_value: LeanStringObject<10> =
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
        m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lean_Elab_Tactic_evalExtractLets___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__3_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_evalExtractLets___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__3_value)
                as *mut LeanObject,
            3488656302031949961 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalExtractLets___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalExtractLets___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalExtractLets___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalExtractLets___closed__6_value: LeanStringObject<9> =
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
        m_data: [108, 111, 99, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_Tactic_evalExtractLets___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__6_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_evalExtractLets___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__6_value)
                as *mut LeanObject,
            1767494567867404924 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalExtractLets___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 118, 97, 108, 69, 120, 116, 114, 97, 99, 116, 76, 101, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value) as *mut LeanObject,2347467322617019280 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__1_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [76, 105, 102, 116, 76, 101, 116, 115, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__1_value) as *mut LeanObject,17681946359195404815 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0_value) as *mut LeanObject;
pub static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            39, 108, 105, 102, 116, 95, 108, 101, 116, 115, 39, 32, 116, 97, 99, 116, 105, 99, 32,
            102, 97, 105, 108, 101, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalLiftLets___closed__0_value: LeanStringObject<9> =
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
        m_data: [108, 105, 102, 116, 76, 101, 116, 115, 0],
    };
static mut l_Lean_Elab_Tactic_evalLiftLets___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLiftLets___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_evalLiftLets___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLiftLets___closed__0_value) as *mut LeanObject,
        4482990907306842784 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalLiftLets___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLiftLets___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalLiftLets___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalLiftLets___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLiftLets___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 76, 105, 102, 116, 76, 101, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0_value) as *mut LeanObject,1479090619291257958 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            39, 108, 101, 116, 95, 116, 111, 95, 104, 97, 118, 101, 39, 32, 116, 97, 99, 116, 105,
            99, 32, 102, 97, 105, 108, 101, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalLetToHave___closed__0_value: LeanStringObject<10> =
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
        m_data: [108, 101, 116, 84, 111, 72, 97, 118, 101, 0],
    };
static mut l_Lean_Elab_Tactic_evalLetToHave___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLetToHave___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExtractLets___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_evalLetToHave___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLetToHave___closed__0_value) as *mut LeanObject,
        13217896183215935516 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalLetToHave___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLetToHave___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalLetToHave___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalLetToHave___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalLetToHave___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 76, 101, 116, 84, 111, 72, 97, 118, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0_value) as *mut LeanObject,16262778937744245571 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(
    mut v_name_3907_: *mut LeanObject,
    mut v_decl_3908_: *mut LeanObject,
    mut v_ref_3909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: u8 = 0;
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3925_: u8 = 0;
    let mut v_unused_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3930_: u8 = 0;
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3911_ = lean_ctor_get(v_decl_3908_, 0);
                v_descr_3912_ = lean_ctor_get(v_decl_3908_, 1);
                v_deprecation_x3f_3913_ = lean_ctor_get(v_decl_3908_, 2);
                v___x_3914_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3915_ = (lean_unbox(v_defValue_3911_) as u8);
                lean_ctor_set_uint8(v___x_3914_, 0 as u32, v___x_3915_);
                lean_inc(v_deprecation_x3f_3913_);
                lean_inc_ref(v_descr_3912_);
                lean_inc_n(v_name_3907_, 2);
                v___x_3916_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3916_, 0, v_name_3907_);
                lean_ctor_set(v___x_3916_, 1, v_ref_3909_);
                lean_ctor_set(v___x_3916_, 2, v___x_3914_);
                lean_ctor_set(v___x_3916_, 3, v_descr_3912_);
                lean_ctor_set(v___x_3916_, 4, v_deprecation_x3f_3913_);
                v___x_3917_ = lean_register_option(v_name_3907_, v___x_3916_);
                if lean_obj_tag(v___x_3917_) == 0 {
                    v_isSharedCheck_3925_ = (!lean_is_exclusive(v___x_3917_)) as u8;
                    if v_isSharedCheck_3925_ == 0 {
                        v_unused_3926_ = lean_ctor_get(v___x_3917_, 0);
                        lean_dec(v_unused_3926_);
                        v___x_3919_ = v___x_3917_;
                        v_isShared_3920_ = v_isSharedCheck_3925_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3917_);
                        v___x_3919_ = lean_box(0);
                        v_isShared_3920_ = v_isSharedCheck_3925_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_3907_);
                    v_a_3927_ = lean_ctor_get(v___x_3917_, 0);
                    v_isSharedCheck_3934_ = (!lean_is_exclusive(v___x_3917_)) as u8;
                    if v_isSharedCheck_3934_ == 0 {
                        v___x_3929_ = v___x_3917_;
                        v_isShared_3930_ = v_isSharedCheck_3934_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3927_);
                        lean_dec(v___x_3917_);
                        v___x_3929_ = lean_box(0);
                        v_isShared_3930_ = v_isSharedCheck_3934_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_3911_);
                v___x_3921_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3921_, 0, v_name_3907_);
                lean_ctor_set(v___x_3921_, 1, v_defValue_3911_);
                if v_isShared_3920_ == 0 {
                    lean_ctor_set(v___x_3919_, 0, v___x_3921_);
                    v___x_3923_ = v___x_3919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
                    v___x_3923_ = v_reuseFailAlloc_3924_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3923_;
            }
            3 => {
                if v_isShared_3930_ == 0 {
                    v___x_3932_ = v___x_3929_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
                    v___x_3932_ = v_reuseFailAlloc_3933_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_3935_: *mut LeanObject,
    mut v_decl_3936_: *mut LeanObject,
    mut v_ref_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3939_: *mut LeanObject = core::ptr::null_mut();
    v_res_3939_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(v_name_3935_, v_decl_3936_, v_ref_3937_);
    lean_dec_ref(v_decl_3936_);
    return v_res_3939_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    v___x_3964_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_;
    v___x_3965_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_;
    v___x_3966_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_;
    v___x_3967_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(v___x_3964_, v___x_3965_, v___x_3966_);
    return v___x_3967_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4____boxed(
    mut v_a_3968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3969_: *mut LeanObject = core::ptr::null_mut();
    v_res_3969_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_();
    return v_res_3969_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(
    mut v_opts_3970_: *mut LeanObject,
    mut v_opt_3971_: *mut LeanObject,
) -> u8 {
    let mut v_name_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    v_name_3972_ = lean_ctor_get(v_opt_3971_, 0);
    v_defValue_3973_ = lean_ctor_get(v_opt_3971_, 1);
    v_map_3974_ = lean_ctor_get(v_opts_3970_, 0);
    v___x_3975_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3974_,
            v_name_3972_,
        );
    if lean_obj_tag(v___x_3975_) == 0 {
        let mut v___x_3976_: u8 = 0;
        v___x_3976_ = (lean_unbox(v_defValue_3973_) as u8);
        return v___x_3976_;
    } else {
        let mut v_val_3977_: *mut LeanObject = core::ptr::null_mut();
        v_val_3977_ = lean_ctor_get(v___x_3975_, 0);
        lean_inc(v_val_3977_);
        lean_dec_ref_known(v___x_3975_, 1);
        if lean_obj_tag(v_val_3977_) == 1 {
            let mut v_v_3978_: u8 = 0;
            v_v_3978_ = lean_ctor_get_uint8(v_val_3977_, 0 as u32);
            lean_dec_ref_known(v_val_3977_, 0);
            return v_v_3978_;
        } else {
            let mut v___x_3979_: u8 = 0;
            lean_dec(v_val_3977_);
            v___x_3979_ = (lean_unbox(v_defValue_3973_) as u8);
            return v___x_3979_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(
    mut v_opts_3980_: *mut LeanObject,
    mut v_opt_3981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3982_: u8 = 0;
    let mut v_r_3983_: *mut LeanObject = core::ptr::null_mut();
    v_res_3982_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_opts_3980_, v_opt_3981_);
    lean_dec_ref(v_opt_3981_);
    lean_dec_ref(v_opts_3980_);
    v_r_3983_ = lean_box((v_res_3982_) as usize);
    return v_r_3983_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(
    mut v_msgData_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
    mut v___y_3986_: *mut LeanObject,
    mut v___y_3987_: *mut LeanObject,
    mut v___y_3988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    v___x_3990_ = lean_st_ref_get(v___y_3988_);
    v_env_3991_ = lean_ctor_get(v___x_3990_, 0);
    lean_inc_ref(v_env_3991_);
    lean_dec(v___x_3990_);
    v___x_3992_ = lean_st_ref_get(v___y_3986_);
    v_mctx_3993_ = lean_ctor_get(v___x_3992_, 0);
    lean_inc_ref(v_mctx_3993_);
    lean_dec(v___x_3992_);
    v_lctx_3994_ = lean_ctor_get(v___y_3985_, 2);
    v_options_3995_ = lean_ctor_get(v___y_3987_, 2);
    lean_inc_ref(v_options_3995_);
    lean_inc_ref(v_lctx_3994_);
    v___x_3996_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3996_, 0, v_env_3991_);
    lean_ctor_set(v___x_3996_, 1, v_mctx_3993_);
    lean_ctor_set(v___x_3996_, 2, v_lctx_3994_);
    lean_ctor_set(v___x_3996_, 3, v_options_3995_);
    v___x_3997_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3997_, 0, v___x_3996_);
    lean_ctor_set(v___x_3997_, 1, v_msgData_3984_);
    v___x_3998_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3998_, 0, v___x_3997_);
    return v___x_3998_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(
    mut v_msgData_3999_: *mut LeanObject,
    mut v___y_4000_: *mut LeanObject,
    mut v___y_4001_: *mut LeanObject,
    mut v___y_4002_: *mut LeanObject,
    mut v___y_4003_: *mut LeanObject,
    mut v___y_4004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4005_: *mut LeanObject = core::ptr::null_mut();
    v_res_4005_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msgData_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
    lean_dec(v___y_4003_);
    lean_dec_ref(v___y_4002_);
    lean_dec(v___y_4001_);
    lean_dec_ref(v___y_4000_);
    return v_res_4005_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(
    mut v___y_4012_: u8,
    mut v_suppressElabErrors_4013_: u8,
    mut v_x_4014_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4014_) == 1 {
        let mut v_pre_4015_: *mut LeanObject = core::ptr::null_mut();
        v_pre_4015_ = lean_ctor_get(v_x_4014_, 0);
        match lean_obj_tag(v_pre_4015_) {
            1 => {
                let mut v_pre_4016_: *mut LeanObject = core::ptr::null_mut();
                v_pre_4016_ = lean_ctor_get(v_pre_4015_, 0);
                match lean_obj_tag(v_pre_4016_) {
                    0 => {
                        let mut v_str_4017_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_4018_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4020_: u8 = 0;
                        v_str_4017_ = lean_ctor_get(v_x_4014_, 1);
                        v_str_4018_ = lean_ctor_get(v_pre_4015_, 1);
                        v___x_4019_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_;
                        v___x_4020_ = lean_string_dec_eq(v_str_4018_, v___x_4019_);
                        if v___x_4020_ == 0 {
                            let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4022_: u8 = 0;
                            v___x_4021_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_;
                            v___x_4022_ = lean_string_dec_eq(v_str_4018_, v___x_4021_);
                            if v___x_4022_ == 0 {
                                return v___y_4012_;
                            } else {
                                let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_4024_: u8 = 0;
                                v___x_4023_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0;
                                v___x_4024_ = lean_string_dec_eq(v_str_4017_, v___x_4023_);
                                if v___x_4024_ == 0 {
                                    return v___y_4012_;
                                } else {
                                    return v_suppressElabErrors_4013_;
                                }
                            }
                        } else {
                            let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4026_: u8 = 0;
                            v___x_4025_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1;
                            v___x_4026_ = lean_string_dec_eq(v_str_4017_, v___x_4025_);
                            if v___x_4026_ == 0 {
                                return v___y_4012_;
                            } else {
                                return v_suppressElabErrors_4013_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_4027_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_4027_ = lean_ctor_get(v_pre_4016_, 0);
                        if lean_obj_tag(v_pre_4027_) == 0 {
                            let mut v_str_4028_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4029_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4030_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4032_: u8 = 0;
                            v_str_4028_ = lean_ctor_get(v_x_4014_, 1);
                            v_str_4029_ = lean_ctor_get(v_pre_4015_, 1);
                            v_str_4030_ = lean_ctor_get(v_pre_4016_, 1);
                            v___x_4031_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2;
                            v___x_4032_ = lean_string_dec_eq(v_str_4030_, v___x_4031_);
                            if v___x_4032_ == 0 {
                                return v___y_4012_;
                            } else {
                                let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_4034_: u8 = 0;
                                v___x_4033_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3;
                                v___x_4034_ = lean_string_dec_eq(v_str_4029_, v___x_4033_);
                                if v___x_4034_ == 0 {
                                    return v___y_4012_;
                                } else {
                                    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_4036_: u8 = 0;
                                    v___x_4035_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4;
                                    v___x_4036_ = lean_string_dec_eq(v_str_4028_, v___x_4035_);
                                    if v___x_4036_ == 0 {
                                        return v___y_4012_;
                                    } else {
                                        return v_suppressElabErrors_4013_;
                                    }
                                }
                            }
                        } else {
                            return v___y_4012_;
                        }
                    }
                    _ => {
                        return v___y_4012_;
                    }
                }
            }
            0 => {
                let mut v_str_4037_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4039_: u8 = 0;
                v_str_4037_ = lean_ctor_get(v_x_4014_, 1);
                v___x_4038_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5;
                v___x_4039_ = lean_string_dec_eq(v_str_4037_, v___x_4038_);
                if v___x_4039_ == 0 {
                    return v___y_4012_;
                } else {
                    return v_suppressElabErrors_4013_;
                }
            }
            _ => {
                return v___y_4012_;
            }
        }
    } else {
        return v___y_4012_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed(
    mut v___y_4040_: *mut LeanObject,
    mut v_suppressElabErrors_4041_: *mut LeanObject,
    mut v_x_4042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6514__boxed_4043_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4044_: u8 = 0;
    let mut v_res_4045_: u8 = 0;
    let mut v_r_4046_: *mut LeanObject = core::ptr::null_mut();
    v___y_6514__boxed_4043_ = (lean_unbox(v___y_4040_) as u8);
    v_suppressElabErrors_boxed_4044_ = (lean_unbox(v_suppressElabErrors_4041_) as u8);
    v_res_4045_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(v___y_6514__boxed_4043_, v_suppressElabErrors_boxed_4044_, v_x_4042_);
    lean_dec(v_x_4042_);
    v_r_4046_ = lean_box((v_res_4045_) as usize);
    return v_r_4046_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(
    mut v_ref_4048_: *mut LeanObject,
    mut v_msgData_4049_: *mut LeanObject,
    mut v_severity_4050_: u8,
    mut v_isSilent_4051_: u8,
    mut v___y_4052_: *mut LeanObject,
    mut v___y_4053_: *mut LeanObject,
    mut v___y_4054_: *mut LeanObject,
    mut v___y_4055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4060_: u8 = 0;
    let mut v___y_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4062_: u8 = 0;
    let mut v___y_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut v___y_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4097_: u8 = 0;
    let mut v___y_4098_: u8 = 0;
    let mut v___y_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4100_: u8 = 0;
    let mut v___y_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4107_: u8 = 0;
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: u8 = 0;
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4117_: u8 = 0;
    let mut v___y_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4121_: u8 = 0;
    let mut v___y_4122_: u8 = 0;
    let mut v___y_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4125_: u8 = 0;
    let mut v___y_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4132_: u8 = 0;
    let mut v___y_4133_: u8 = 0;
    let mut v___y_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4136_: u8 = 0;
    let mut v_ref_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: u8 = 0;
    let mut v___y_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4144_: u8 = 0;
    let mut v___y_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4148_: u8 = 0;
    let mut v___y_4149_: u8 = 0;
    let mut v___y_4151_: u8 = 0;
    let mut v_fileName_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4156_: u8 = 0;
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: u8 = 0;
    let mut v___x_4161_: u8 = 0;
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: u8 = 0;
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: u8 = 0;
    let mut v___x_4167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4141_ = 2;
                v___x_4166_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4050_, v___x_4141_);
                if v___x_4166_ == 0 {
                    v___y_4151_ = v___x_4166_;
                    state = 10;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_4049_);
                    v___x_4167_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4049_);
                    v___y_4151_ = v___x_4167_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4067_ = lean_st_ref_take(v___y_4066_);
                v_currNamespace_4068_ = lean_ctor_get(v___y_4065_, 6);
                v_openDecls_4069_ = lean_ctor_get(v___y_4065_, 7);
                v_env_4070_ = lean_ctor_get(v___x_4067_, 0);
                v_nextMacroScope_4071_ = lean_ctor_get(v___x_4067_, 1);
                v_ngen_4072_ = lean_ctor_get(v___x_4067_, 2);
                v_auxDeclNGen_4073_ = lean_ctor_get(v___x_4067_, 3);
                v_traceState_4074_ = lean_ctor_get(v___x_4067_, 4);
                v_cache_4075_ = lean_ctor_get(v___x_4067_, 5);
                v_messages_4076_ = lean_ctor_get(v___x_4067_, 6);
                v_infoState_4077_ = lean_ctor_get(v___x_4067_, 7);
                v_snapshotTasks_4078_ = lean_ctor_get(v___x_4067_, 8);
                v_isSharedCheck_4092_ = (!lean_is_exclusive(v___x_4067_)) as u8;
                if v_isSharedCheck_4092_ == 0 {
                    v___x_4080_ = v___x_4067_;
                    v_isShared_4081_ = v_isSharedCheck_4092_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4078_);
                    lean_inc(v_infoState_4077_);
                    lean_inc(v_messages_4076_);
                    lean_inc(v_cache_4075_);
                    lean_inc(v_traceState_4074_);
                    lean_inc(v_auxDeclNGen_4073_);
                    lean_inc(v_ngen_4072_);
                    lean_inc(v_nextMacroScope_4071_);
                    lean_inc(v_env_4070_);
                    lean_dec(v___x_4067_);
                    v___x_4080_ = lean_box(0);
                    v_isShared_4081_ = v_isSharedCheck_4092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_4069_);
                lean_inc(v_currNamespace_4068_);
                v___x_4082_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4082_, 0, v_currNamespace_4068_);
                lean_ctor_set(v___x_4082_, 1, v_openDecls_4069_);
                v___x_4083_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4083_, 0, v___x_4082_);
                lean_ctor_set(v___x_4083_, 1, v___y_4064_);
                lean_inc_ref(v___y_4059_);
                lean_inc_ref(v___y_4058_);
                v___x_4084_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_4084_, 0, v___y_4058_);
                lean_ctor_set(v___x_4084_, 1, v___y_4063_);
                lean_ctor_set(v___x_4084_, 2, v___y_4061_);
                lean_ctor_set(v___x_4084_, 3, v___y_4059_);
                lean_ctor_set(v___x_4084_, 4, v___x_4083_);
                lean_ctor_set_uint8(
                    v___x_4084_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_4060_,
                );
                lean_ctor_set_uint8(
                    v___x_4084_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_4062_,
                );
                lean_ctor_set_uint8(
                    v___x_4084_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4051_,
                );
                v___x_4085_ = l_Lean_MessageLog_add(v___x_4084_, v_messages_4076_);
                if v_isShared_4081_ == 0 {
                    lean_ctor_set(v___x_4080_, 6, v___x_4085_);
                    v___x_4087_ = v___x_4080_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_env_4070_);
                    lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_nextMacroScope_4071_);
                    lean_ctor_set(v_reuseFailAlloc_4091_, 2, v_ngen_4072_);
                    lean_ctor_set(v_reuseFailAlloc_4091_, 3, v_auxDeclNGen_4073_);
                    lean_ctor_set(v_reuseFailAlloc_4091_, 4, v_traceState_4074_);
                    lean_ctor_set(v_reuseFailAlloc_4091_, 5, v_cache_4075_);
                    lean_ctor_set(v_reuseFailAlloc_4091_, 6, v___x_4085_);
                    lean_ctor_set(v_reuseFailAlloc_4091_, 7, v_infoState_4077_);
                    lean_ctor_set(v_reuseFailAlloc_4091_, 8, v_snapshotTasks_4078_);
                    v___x_4087_ = v_reuseFailAlloc_4091_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4088_ = lean_st_ref_set(v___y_4066_, v___x_4087_);
                v___x_4089_ = lean_box(0);
                v___x_4090_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4090_, 0, v___x_4089_);
                return v___x_4090_;
            }
            4 => {
                v___x_4102_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4049_,
                    );
                v___x_4103_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v___x_4102_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
                v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
                v_isSharedCheck_4117_ = (!lean_is_exclusive(v___x_4103_)) as u8;
                if v_isSharedCheck_4117_ == 0 {
                    v___x_4106_ = v___x_4103_;
                    v_isShared_4107_ = v_isSharedCheck_4117_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_4104_);
                    lean_dec(v___x_4103_);
                    v___x_4106_ = lean_box(0);
                    v_isShared_4107_ = v_isSharedCheck_4117_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_4099_, 2);
                v___x_4108_ = l_Lean_FileMap_toPosition(v___y_4099_, v___y_4096_);
                lean_dec(v___y_4096_);
                v___x_4109_ = l_Lean_FileMap_toPosition(v___y_4099_, v___y_4101_);
                lean_dec(v___y_4101_);
                v___x_4110_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4110_, 0, v___x_4109_);
                v___x_4111_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0;
                if v___y_4097_ == 0 {
                    lean_del_object(v___x_4106_);
                    lean_dec_ref(v___y_4094_);
                    v___y_4058_ = v___y_4095_;
                    v___y_4059_ = v___x_4111_;
                    v___y_4060_ = v___y_4098_;
                    v___y_4061_ = v___x_4110_;
                    v___y_4062_ = v___y_4100_;
                    v___y_4063_ = v___x_4108_;
                    v___y_4064_ = v_a_4104_;
                    v___y_4065_ = v___y_4054_;
                    v___y_4066_ = v___y_4055_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4104_);
                    v___x_4112_ = l_Lean_MessageData_hasTag(v___y_4094_, v_a_4104_);
                    if v___x_4112_ == 0 {
                        lean_dec_ref_known(v___x_4110_, 1);
                        lean_dec_ref(v___x_4108_);
                        lean_dec(v_a_4104_);
                        v___x_4113_ = lean_box(0);
                        if v_isShared_4107_ == 0 {
                            lean_ctor_set(v___x_4106_, 0, v___x_4113_);
                            v___x_4115_ = v___x_4106_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4113_);
                            v___x_4115_ = v_reuseFailAlloc_4116_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4106_);
                        v___y_4058_ = v___y_4095_;
                        v___y_4059_ = v___x_4111_;
                        v___y_4060_ = v___y_4098_;
                        v___y_4061_ = v___x_4110_;
                        v___y_4062_ = v___y_4100_;
                        v___y_4063_ = v___x_4108_;
                        v___y_4064_ = v_a_4104_;
                        v___y_4065_ = v___y_4054_;
                        v___y_4066_ = v___y_4055_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4115_;
            }
            7 => {
                v___x_4127_ = l_Lean_Syntax_getTailPos_x3f(v___y_4124_, v___y_4122_);
                lean_dec(v___y_4124_);
                if lean_obj_tag(v___x_4127_) == 0 {
                    lean_inc(v___y_4126_);
                    v___y_4094_ = v___y_4119_;
                    v___y_4095_ = v___y_4120_;
                    v___y_4096_ = v___y_4126_;
                    v___y_4097_ = v___y_4121_;
                    v___y_4098_ = v___y_4122_;
                    v___y_4099_ = v___y_4123_;
                    v___y_4100_ = v___y_4125_;
                    v___y_4101_ = v___y_4126_;
                    state = 4;
                    continue;
                } else {
                    v_val_4128_ = lean_ctor_get(v___x_4127_, 0);
                    lean_inc(v_val_4128_);
                    lean_dec_ref_known(v___x_4127_, 1);
                    v___y_4094_ = v___y_4119_;
                    v___y_4095_ = v___y_4120_;
                    v___y_4096_ = v___y_4126_;
                    v___y_4097_ = v___y_4121_;
                    v___y_4098_ = v___y_4122_;
                    v___y_4099_ = v___y_4123_;
                    v___y_4100_ = v___y_4125_;
                    v___y_4101_ = v_val_4128_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_4137_ = l_Lean_replaceRef(v_ref_4048_, v___y_4134_);
                v___x_4138_ = l_Lean_Syntax_getPos_x3f(v_ref_4137_, v___y_4133_);
                if lean_obj_tag(v___x_4138_) == 0 {
                    v___x_4139_ = lean_unsigned_to_nat(0);
                    v___y_4119_ = v___y_4130_;
                    v___y_4120_ = v___y_4131_;
                    v___y_4121_ = v___y_4132_;
                    v___y_4122_ = v___y_4133_;
                    v___y_4123_ = v___y_4135_;
                    v___y_4124_ = v_ref_4137_;
                    v___y_4125_ = v___y_4136_;
                    v___y_4126_ = v___x_4139_;
                    state = 7;
                    continue;
                } else {
                    v_val_4140_ = lean_ctor_get(v___x_4138_, 0);
                    lean_inc(v_val_4140_);
                    lean_dec_ref_known(v___x_4138_, 1);
                    v___y_4119_ = v___y_4130_;
                    v___y_4120_ = v___y_4131_;
                    v___y_4121_ = v___y_4132_;
                    v___y_4122_ = v___y_4133_;
                    v___y_4123_ = v___y_4135_;
                    v___y_4124_ = v_ref_4137_;
                    v___y_4125_ = v___y_4136_;
                    v___y_4126_ = v_val_4140_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_4149_ == 0 {
                    v___y_4130_ = v___y_4147_;
                    v___y_4131_ = v___y_4143_;
                    v___y_4132_ = v___y_4144_;
                    v___y_4133_ = v___y_4148_;
                    v___y_4134_ = v___y_4145_;
                    v___y_4135_ = v___y_4146_;
                    v___y_4136_ = v_severity_4050_;
                    state = 8;
                    continue;
                } else {
                    v___y_4130_ = v___y_4147_;
                    v___y_4131_ = v___y_4143_;
                    v___y_4132_ = v___y_4144_;
                    v___y_4133_ = v___y_4148_;
                    v___y_4134_ = v___y_4145_;
                    v___y_4135_ = v___y_4146_;
                    v___y_4136_ = v___x_4141_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_4151_ == 0 {
                    v_fileName_4152_ = lean_ctor_get(v___y_4054_, 0);
                    v_fileMap_4153_ = lean_ctor_get(v___y_4054_, 1);
                    v_options_4154_ = lean_ctor_get(v___y_4054_, 2);
                    v_ref_4155_ = lean_ctor_get(v___y_4054_, 5);
                    v_suppressElabErrors_4156_ = lean_ctor_get_uint8(
                        v___y_4054_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4157_ = lean_box((v___y_4151_) as usize);
                    v___x_4158_ = lean_box((v_suppressElabErrors_4156_) as usize);
                    v___f_4159_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_4159_, 0, v___x_4157_);
                    lean_closure_set(v___f_4159_, 1, v___x_4158_);
                    v___x_4160_ = 1;
                    v___x_4161_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4050_, v___x_4160_);
                    if v___x_4161_ == 0 {
                        v___y_4143_ = v_fileName_4152_;
                        v___y_4144_ = v_suppressElabErrors_4156_;
                        v___y_4145_ = v_ref_4155_;
                        v___y_4146_ = v_fileMap_4153_;
                        v___y_4147_ = v___f_4159_;
                        v___y_4148_ = v___y_4151_;
                        v___y_4149_ = v___x_4161_;
                        state = 9;
                        continue;
                    } else {
                        v___x_4162_ = l_Lean_warningAsError;
                        v___x_4163_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_options_4154_, v___x_4162_);
                        v___y_4143_ = v_fileName_4152_;
                        v___y_4144_ = v_suppressElabErrors_4156_;
                        v___y_4145_ = v_ref_4155_;
                        v___y_4146_ = v_fileMap_4153_;
                        v___y_4147_ = v___f_4159_;
                        v___y_4148_ = v___y_4151_;
                        v___y_4149_ = v___x_4163_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_4049_);
                    v___x_4164_ = lean_box(0);
                    v___x_4165_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4165_, 0, v___x_4164_);
                    return v___x_4165_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_ref_4168_: *mut LeanObject,
    mut v_msgData_4169_: *mut LeanObject,
    mut v_severity_4170_: *mut LeanObject,
    mut v_isSilent_4171_: *mut LeanObject,
    mut v___y_4172_: *mut LeanObject,
    mut v___y_4173_: *mut LeanObject,
    mut v___y_4174_: *mut LeanObject,
    mut v___y_4175_: *mut LeanObject,
    mut v___y_4176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_4177_: u8 = 0;
    let mut v_isSilent_boxed_4178_: u8 = 0;
    let mut v_res_4179_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_4177_ = (lean_unbox(v_severity_4170_) as u8);
    v_isSilent_boxed_4178_ = (lean_unbox(v_isSilent_4171_) as u8);
    v_res_4179_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4168_, v_msgData_4169_, v_severity_boxed_4177_, v_isSilent_boxed_4178_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
    lean_dec(v___y_4175_);
    lean_dec_ref(v___y_4174_);
    lean_dec(v___y_4173_);
    lean_dec_ref(v___y_4172_);
    lean_dec(v_ref_4168_);
    return v_res_4179_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(
    mut v_ref_4180_: *mut LeanObject,
    mut v_msgData_4181_: *mut LeanObject,
    mut v___y_4182_: *mut LeanObject,
    mut v___y_4183_: *mut LeanObject,
    mut v___y_4184_: *mut LeanObject,
    mut v___y_4185_: *mut LeanObject,
    mut v___y_4186_: *mut LeanObject,
    mut v___y_4187_: *mut LeanObject,
    mut v___y_4188_: *mut LeanObject,
    mut v___y_4189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4191_: u8 = 0;
    let mut v___x_4192_: u8 = 0;
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    v___x_4191_ = 1;
    v___x_4192_ = 0;
    v___x_4193_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4180_, v_msgData_4181_, v___x_4191_, v___x_4192_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
    return v___x_4193_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3___boxed(
    mut v_ref_4194_: *mut LeanObject,
    mut v_msgData_4195_: *mut LeanObject,
    mut v___y_4196_: *mut LeanObject,
    mut v___y_4197_: *mut LeanObject,
    mut v___y_4198_: *mut LeanObject,
    mut v___y_4199_: *mut LeanObject,
    mut v___y_4200_: *mut LeanObject,
    mut v___y_4201_: *mut LeanObject,
    mut v___y_4202_: *mut LeanObject,
    mut v___y_4203_: *mut LeanObject,
    mut v___y_4204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4205_: *mut LeanObject = core::ptr::null_mut();
    v_res_4205_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_ref_4194_, v_msgData_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
    lean_dec(v___y_4203_);
    lean_dec_ref(v___y_4202_);
    lean_dec(v___y_4201_);
    lean_dec_ref(v___y_4200_);
    lean_dec(v___y_4199_);
    lean_dec_ref(v___y_4198_);
    lean_dec(v___y_4197_);
    lean_dec_ref(v___y_4196_);
    lean_dec(v_ref_4194_);
    return v_res_4205_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    v___x_4207_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0;
    v___x_4208_ = l_Lean_stringToMessageData(v___x_4207_);
    return v___x_4208_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    v___x_4210_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2;
    v___x_4211_ = l_Lean_stringToMessageData(v___x_4210_);
    return v___x_4211_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(
    mut v_linterOption_4212_: *mut LeanObject,
    mut v_stx_4213_: *mut LeanObject,
    mut v_msg_4214_: *mut LeanObject,
    mut v___y_4215_: *mut LeanObject,
    mut v___y_4216_: *mut LeanObject,
    mut v___y_4217_: *mut LeanObject,
    mut v___y_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
    mut v___y_4220_: *mut LeanObject,
    mut v___y_4221_: *mut LeanObject,
    mut v___y_4222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4227_: u8 = 0;
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disable_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut v_unused_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_4224_ = lean_ctor_get(v_linterOption_4212_, 0);
                v_isSharedCheck_4241_ = (!lean_is_exclusive(v_linterOption_4212_)) as u8;
                if v_isSharedCheck_4241_ == 0 {
                    v_unused_4242_ = lean_ctor_get(v_linterOption_4212_, 1);
                    lean_dec(v_unused_4242_);
                    v___x_4226_ = v_linterOption_4212_;
                    v_isShared_4227_ = v_isSharedCheck_4241_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_4224_);
                    lean_dec(v_linterOption_4212_);
                    v___x_4226_ = lean_box(0);
                    v_isShared_4227_ = v_isSharedCheck_4241_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4228_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1);
                lean_inc(v_name_4224_);
                v___x_4229_ = l_Lean_MessageData_ofName(v_name_4224_);
                if v_isShared_4227_ == 0 {
                    lean_ctor_set_tag(v___x_4226_, 7);
                    lean_ctor_set(v___x_4226_, 1, v___x_4229_);
                    lean_ctor_set(v___x_4226_, 0, v___x_4228_);
                    v___x_4231_ = v___x_4226_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4240_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4228_);
                    lean_ctor_set(v_reuseFailAlloc_4240_, 1, v___x_4229_);
                    v___x_4231_ = v_reuseFailAlloc_4240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4232_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3);
                v___x_4233_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4233_, 0, v___x_4231_);
                lean_ctor_set(v___x_4233_, 1, v___x_4232_);
                v_disable_4234_ = l_Lean_MessageData_note(v___x_4233_);
                v___x_4235_ = l_Lean_Linter_linterMessageTag;
                v___x_4236_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4236_, 0, v_msg_4214_);
                lean_ctor_set(v___x_4236_, 1, v_disable_4234_);
                v___x_4237_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_4237_, 0, v___x_4235_);
                lean_ctor_set(v___x_4237_, 1, v___x_4236_);
                v___x_4238_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_4238_, 0, v_name_4224_);
                lean_ctor_set(v___x_4238_, 1, v___x_4237_);
                v___x_4239_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_stx_4213_, v___x_4238_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
                return v___x_4239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___boxed(
    mut v_linterOption_4243_: *mut LeanObject,
    mut v_stx_4244_: *mut LeanObject,
    mut v_msg_4245_: *mut LeanObject,
    mut v___y_4246_: *mut LeanObject,
    mut v___y_4247_: *mut LeanObject,
    mut v___y_4248_: *mut LeanObject,
    mut v___y_4249_: *mut LeanObject,
    mut v___y_4250_: *mut LeanObject,
    mut v___y_4251_: *mut LeanObject,
    mut v___y_4252_: *mut LeanObject,
    mut v___y_4253_: *mut LeanObject,
    mut v___y_4254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4255_: *mut LeanObject = core::ptr::null_mut();
    v_res_4255_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_4243_, v_stx_4244_, v_msg_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
    lean_dec(v___y_4253_);
    lean_dec_ref(v___y_4252_);
    lean_dec(v___y_4251_);
    lean_dec_ref(v___y_4250_);
    lean_dec(v___y_4249_);
    lean_dec_ref(v___y_4248_);
    lean_dec(v___y_4247_);
    lean_dec_ref(v___y_4246_);
    lean_dec(v_stx_4244_);
    return v_res_4255_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(
    mut v_o_4256_: *mut LeanObject,
    mut v___y_4257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linterSets_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    v___x_4259_ = lean_st_ref_get(v___y_4257_);
    v_env_4260_ = lean_ctor_get(v___x_4259_, 0);
    lean_inc_ref(v_env_4260_);
    lean_dec(v___x_4259_);
    v___x_4261_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_4262_ = lean_ctor_get(v___x_4261_, 0);
    v_asyncMode_4263_ = lean_ctor_get(v_toEnvExtension_4262_, 2);
    v___x_4264_ = lean_box(1);
    v___x_4265_ = lean_box(0);
    v_linterSets_4266_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_4264_,
        v___x_4261_,
        v_env_4260_,
        v_asyncMode_4263_,
        v___x_4265_,
    );
    v___x_4267_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4267_, 0, v_o_4256_);
    lean_ctor_set(v___x_4267_, 1, v_linterSets_4266_);
    v___x_4268_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4268_, 0, v___x_4267_);
    return v___x_4268_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_o_4269_: *mut LeanObject,
    mut v___y_4270_: *mut LeanObject,
    mut v___y_4271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4272_: *mut LeanObject = core::ptr::null_mut();
    v_res_4272_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_4269_, v___y_4270_);
    lean_dec(v___y_4270_);
    return v_res_4272_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(
    mut v___y_4273_: *mut LeanObject,
    mut v___y_4274_: *mut LeanObject,
    mut v___y_4275_: *mut LeanObject,
    mut v___y_4276_: *mut LeanObject,
    mut v___y_4277_: *mut LeanObject,
    mut v___y_4278_: *mut LeanObject,
    mut v___y_4279_: *mut LeanObject,
    mut v___y_4280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    v_options_4282_ = lean_ctor_get(v___y_4279_, 2);
    lean_inc_ref(v_options_4282_);
    v___x_4283_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_options_4282_, v___y_4280_);
    return v___x_4283_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0___boxed(
    mut v___y_4284_: *mut LeanObject,
    mut v___y_4285_: *mut LeanObject,
    mut v___y_4286_: *mut LeanObject,
    mut v___y_4287_: *mut LeanObject,
    mut v___y_4288_: *mut LeanObject,
    mut v___y_4289_: *mut LeanObject,
    mut v___y_4290_: *mut LeanObject,
    mut v___y_4291_: *mut LeanObject,
    mut v___y_4292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4293_: *mut LeanObject = core::ptr::null_mut();
    v_res_4293_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
    lean_dec(v___y_4291_);
    lean_dec_ref(v___y_4290_);
    lean_dec(v___y_4289_);
    lean_dec_ref(v___y_4288_);
    lean_dec(v___y_4287_);
    lean_dec_ref(v___y_4286_);
    lean_dec(v___y_4285_);
    lean_dec_ref(v___y_4284_);
    return v_res_4293_;
}
pub unsafe fn l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(
    mut v_linterOption_4294_: *mut LeanObject,
    mut v_stx_4295_: *mut LeanObject,
    mut v_msg_4296_: *mut LeanObject,
    mut v___y_4297_: *mut LeanObject,
    mut v___y_4298_: *mut LeanObject,
    mut v___y_4299_: *mut LeanObject,
    mut v___y_4300_: *mut LeanObject,
    mut v___y_4301_: *mut LeanObject,
    mut v___y_4302_: *mut LeanObject,
    mut v___y_4303_: *mut LeanObject,
    mut v___y_4304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4310_: u8 = 0;
    let mut v___x_4311_: u8 = 0;
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4306_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
                v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
                v_isSharedCheck_4317_ = (!lean_is_exclusive(v___x_4306_)) as u8;
                if v_isSharedCheck_4317_ == 0 {
                    v___x_4309_ = v___x_4306_;
                    v_isShared_4310_ = v_isSharedCheck_4317_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4307_);
                    lean_dec(v___x_4306_);
                    v___x_4309_ = lean_box(0);
                    v_isShared_4310_ = v_isSharedCheck_4317_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4311_ = l_Lean_Linter_getLinterValue(v_linterOption_4294_, v_a_4307_);
                lean_dec(v_a_4307_);
                if v___x_4311_ == 0 {
                    lean_dec_ref(v_msg_4296_);
                    lean_dec_ref(v_linterOption_4294_);
                    v___x_4312_ = lean_box(0);
                    if v_isShared_4310_ == 0 {
                        lean_ctor_set(v___x_4309_, 0, v___x_4312_);
                        v___x_4314_ = v___x_4309_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4312_);
                        v___x_4314_ = v_reuseFailAlloc_4315_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4309_);
                    v___x_4316_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_4294_, v_stx_4295_, v_msg_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
                    return v___x_4316_;
                }
            }
            2 => {
                return v___x_4314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0___boxed(
    mut v_linterOption_4318_: *mut LeanObject,
    mut v_stx_4319_: *mut LeanObject,
    mut v_msg_4320_: *mut LeanObject,
    mut v___y_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
    mut v___y_4329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4330_: *mut LeanObject = core::ptr::null_mut();
    v_res_4330_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(
        v_linterOption_4318_,
        v_stx_4319_,
        v_msg_4320_,
        v___y_4321_,
        v___y_4322_,
        v___y_4323_,
        v___y_4324_,
        v___y_4325_,
        v___y_4326_,
        v___y_4327_,
        v___y_4328_,
    );
    lean_dec(v___y_4328_);
    lean_dec_ref(v___y_4327_);
    lean_dec(v___y_4326_);
    lean_dec_ref(v___y_4325_);
    lean_dec(v___y_4324_);
    lean_dec_ref(v___y_4323_);
    lean_dec(v___y_4322_);
    lean_dec_ref(v___y_4321_);
    lean_dec(v_stx_4319_);
    return v_res_4330_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    v___x_4332_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0;
    v___x_4333_ = l_Lean_stringToMessageData(v___x_4332_);
    return v___x_4333_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(
    mut v_upperBound_4334_: *mut LeanObject,
    mut v_fvars_4335_: *mut LeanObject,
    mut v_ids_4336_: *mut LeanObject,
    mut v_a_4337_: *mut LeanObject,
    mut v_b_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
    mut v___y_4341_: *mut LeanObject,
    mut v___y_4342_: *mut LeanObject,
    mut v___y_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: u8 = 0;
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: u8 = 0;
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4353_ = lean_nat_dec_lt(v_a_4337_, v_upperBound_4334_);
                if v___x_4353_ == 0 {
                    lean_dec(v_a_4337_);
                    v___x_4354_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4354_, 0, v_b_4338_);
                    return v___x_4354_;
                } else {
                    v___x_4355_ = lean_box(0);
                    v___x_4356_ = lean_array_get_size(v_fvars_4335_);
                    v___x_4357_ = lean_nat_dec_lt(v_a_4337_, v___x_4356_);
                    if v___x_4357_ == 0 {
                        v___x_4358_ = l_Lean_Elab_Tactic_linter_tactic_unusedName;
                        v___x_4359_ = lean_array_fget_borrowed(v_ids_4336_, v_a_4337_);
                        v___x_4360_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1);
                        v___x_4361_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v___x_4358_, v___x_4359_, v___x_4360_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                        if lean_obj_tag(v___x_4361_) == 0 {
                            lean_dec_ref_known(v___x_4361_, 1);
                            v_a_4349_ = v___x_4355_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_4337_);
                            return v___x_4361_;
                        }
                    } else {
                        v___x_4362_ = lean_array_fget_borrowed(v_ids_4336_, v_a_4337_);
                        v___x_4363_ = lean_array_fget_borrowed(v_fvars_4335_, v_a_4337_);
                        lean_inc(v___x_4363_);
                        v___x_4364_ = l_Lean_mkFVar(v___x_4363_);
                        lean_inc(v___x_4362_);
                        v___x_4365_ = l_Lean_Elab_Term_addLocalVarInfo(
                            v___x_4362_,
                            v___x_4364_,
                            v___y_4341_,
                            v___y_4342_,
                            v___y_4343_,
                            v___y_4344_,
                            v___y_4345_,
                            v___y_4346_,
                        );
                        if lean_obj_tag(v___x_4365_) == 0 {
                            lean_dec_ref_known(v___x_4365_, 1);
                            v_a_4349_ = v___x_4355_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_4337_);
                            return v___x_4365_;
                        }
                    }
                }
            }
            1 => {
                v___x_4350_ = lean_unsigned_to_nat(1);
                v___x_4351_ = lean_nat_add(v_a_4337_, v___x_4350_);
                lean_dec(v_a_4337_);
                v_a_4337_ = v___x_4351_;
                v_b_4338_ = v_a_4349_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___boxed(
    mut v_upperBound_4366_: *mut LeanObject,
    mut v_fvars_4367_: *mut LeanObject,
    mut v_ids_4368_: *mut LeanObject,
    mut v_a_4369_: *mut LeanObject,
    mut v_b_4370_: *mut LeanObject,
    mut v___y_4371_: *mut LeanObject,
    mut v___y_4372_: *mut LeanObject,
    mut v___y_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
    mut v___y_4375_: *mut LeanObject,
    mut v___y_4376_: *mut LeanObject,
    mut v___y_4377_: *mut LeanObject,
    mut v___y_4378_: *mut LeanObject,
    mut v___y_4379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4380_: *mut LeanObject = core::ptr::null_mut();
    v_res_4380_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_4366_, v_fvars_4367_, v_ids_4368_, v_a_4369_, v_b_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
    lean_dec(v___y_4378_);
    lean_dec_ref(v___y_4377_);
    lean_dec(v___y_4376_);
    lean_dec_ref(v___y_4375_);
    lean_dec(v___y_4374_);
    lean_dec_ref(v___y_4373_);
    lean_dec(v___y_4372_);
    lean_dec_ref(v___y_4371_);
    lean_dec_ref(v_ids_4368_);
    lean_dec_ref(v_fvars_4367_);
    lean_dec(v_upperBound_4366_);
    return v_res_4380_;
}
pub unsafe fn l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(
    mut v___x_4381_: *mut LeanObject,
    mut v_fvars_4382_: *mut LeanObject,
    mut v_ids_4383_: *mut LeanObject,
    mut v___x_4384_: *mut LeanObject,
    mut v___y_4385_: *mut LeanObject,
    mut v___y_4386_: *mut LeanObject,
    mut v___y_4387_: *mut LeanObject,
    mut v___y_4388_: *mut LeanObject,
    mut v___y_4389_: *mut LeanObject,
    mut v___y_4390_: *mut LeanObject,
    mut v___y_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4402_: u8 = 0;
    let mut v_unused_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4394_ = lean_unsigned_to_nat(0);
                v___x_4395_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v___x_4381_, v_fvars_4382_, v_ids_4383_, v___x_4394_, v___x_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
                if lean_obj_tag(v___x_4395_) == 0 {
                    v_isSharedCheck_4402_ = (!lean_is_exclusive(v___x_4395_)) as u8;
                    if v_isSharedCheck_4402_ == 0 {
                        v_unused_4403_ = lean_ctor_get(v___x_4395_, 0);
                        lean_dec(v_unused_4403_);
                        v___x_4397_ = v___x_4395_;
                        v_isShared_4398_ = v_isSharedCheck_4402_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_4395_);
                        v___x_4397_ = lean_box(0);
                        v_isShared_4398_ = v_isSharedCheck_4402_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4395_;
                }
            }
            1 => {
                if v_isShared_4398_ == 0 {
                    lean_ctor_set(v___x_4397_, 0, v___x_4384_);
                    v___x_4400_ = v___x_4397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4384_);
                    v___x_4400_ = v_reuseFailAlloc_4401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed(
    mut v___x_4404_: *mut LeanObject,
    mut v_fvars_4405_: *mut LeanObject,
    mut v_ids_4406_: *mut LeanObject,
    mut v___x_4407_: *mut LeanObject,
    mut v___y_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
    mut v___y_4411_: *mut LeanObject,
    mut v___y_4412_: *mut LeanObject,
    mut v___y_4413_: *mut LeanObject,
    mut v___y_4414_: *mut LeanObject,
    mut v___y_4415_: *mut LeanObject,
    mut v___y_4416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4417_: *mut LeanObject = core::ptr::null_mut();
    v_res_4417_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(
        v___x_4404_,
        v_fvars_4405_,
        v_ids_4406_,
        v___x_4407_,
        v___y_4408_,
        v___y_4409_,
        v___y_4410_,
        v___y_4411_,
        v___y_4412_,
        v___y_4413_,
        v___y_4414_,
        v___y_4415_,
    );
    lean_dec(v___y_4415_);
    lean_dec_ref(v___y_4414_);
    lean_dec(v___y_4413_);
    lean_dec_ref(v___y_4412_);
    lean_dec(v___y_4411_);
    lean_dec_ref(v___y_4410_);
    lean_dec(v___y_4409_);
    lean_dec_ref(v___y_4408_);
    lean_dec_ref(v_ids_4406_);
    lean_dec_ref(v_fvars_4405_);
    lean_dec(v___x_4404_);
    return v_res_4417_;
}
pub unsafe fn l_Lean_Elab_Tactic_extractLetsAddVarInfo(
    mut v_ids_4418_: *mut LeanObject,
    mut v_fvars_4419_: *mut LeanObject,
    mut v_a_4420_: *mut LeanObject,
    mut v_a_4421_: *mut LeanObject,
    mut v_a_4422_: *mut LeanObject,
    mut v_a_4423_: *mut LeanObject,
    mut v_a_4424_: *mut LeanObject,
    mut v_a_4425_: *mut LeanObject,
    mut v_a_4426_: *mut LeanObject,
    mut v_a_4427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    v___x_4429_ = lean_array_get_size(v_ids_4418_);
    v___x_4430_ = lean_box(0);
    v___f_4431_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed as *mut core::ffi::c_void,
        13,
        4,
    );
    lean_closure_set(v___f_4431_, 0, v___x_4429_);
    lean_closure_set(v___f_4431_, 1, v_fvars_4419_);
    lean_closure_set(v___f_4431_, 2, v_ids_4418_);
    lean_closure_set(v___f_4431_, 3, v___x_4430_);
    v___x_4432_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_4431_,
        v_a_4420_,
        v_a_4421_,
        v_a_4422_,
        v_a_4423_,
        v_a_4424_,
        v_a_4425_,
        v_a_4426_,
        v_a_4427_,
    );
    return v___x_4432_;
}
pub unsafe fn l_Lean_Elab_Tactic_extractLetsAddVarInfo___boxed(
    mut v_ids_4433_: *mut LeanObject,
    mut v_fvars_4434_: *mut LeanObject,
    mut v_a_4435_: *mut LeanObject,
    mut v_a_4436_: *mut LeanObject,
    mut v_a_4437_: *mut LeanObject,
    mut v_a_4438_: *mut LeanObject,
    mut v_a_4439_: *mut LeanObject,
    mut v_a_4440_: *mut LeanObject,
    mut v_a_4441_: *mut LeanObject,
    mut v_a_4442_: *mut LeanObject,
    mut v_a_4443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4444_: *mut LeanObject = core::ptr::null_mut();
    v_res_4444_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(
        v_ids_4433_,
        v_fvars_4434_,
        v_a_4435_,
        v_a_4436_,
        v_a_4437_,
        v_a_4438_,
        v_a_4439_,
        v_a_4440_,
        v_a_4441_,
        v_a_4442_,
    );
    lean_dec(v_a_4442_);
    lean_dec_ref(v_a_4441_);
    lean_dec(v_a_4440_);
    lean_dec_ref(v_a_4439_);
    lean_dec(v_a_4438_);
    lean_dec_ref(v_a_4437_);
    lean_dec(v_a_4436_);
    lean_dec_ref(v_a_4435_);
    return v_res_4444_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(
    mut v_upperBound_4445_: *mut LeanObject,
    mut v_fvars_4446_: *mut LeanObject,
    mut v_ids_4447_: *mut LeanObject,
    mut v_inst_4448_: *mut LeanObject,
    mut v_R_4449_: *mut LeanObject,
    mut v_a_4450_: *mut LeanObject,
    mut v_b_4451_: *mut LeanObject,
    mut v_c_4452_: *mut LeanObject,
    mut v___y_4453_: *mut LeanObject,
    mut v___y_4454_: *mut LeanObject,
    mut v___y_4455_: *mut LeanObject,
    mut v___y_4456_: *mut LeanObject,
    mut v___y_4457_: *mut LeanObject,
    mut v___y_4458_: *mut LeanObject,
    mut v___y_4459_: *mut LeanObject,
    mut v___y_4460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    v___x_4462_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_4445_, v_fvars_4446_, v_ids_4447_, v_a_4450_, v_b_4451_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
    return v___x_4462_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_4463_: *mut LeanObject = *_args.add(0);
    let mut v_fvars_4464_: *mut LeanObject = *_args.add(1);
    let mut v_ids_4465_: *mut LeanObject = *_args.add(2);
    let mut v_inst_4466_: *mut LeanObject = *_args.add(3);
    let mut v_R_4467_: *mut LeanObject = *_args.add(4);
    let mut v_a_4468_: *mut LeanObject = *_args.add(5);
    let mut v_b_4469_: *mut LeanObject = *_args.add(6);
    let mut v_c_4470_: *mut LeanObject = *_args.add(7);
    let mut v___y_4471_: *mut LeanObject = *_args.add(8);
    let mut v___y_4472_: *mut LeanObject = *_args.add(9);
    let mut v___y_4473_: *mut LeanObject = *_args.add(10);
    let mut v___y_4474_: *mut LeanObject = *_args.add(11);
    let mut v___y_4475_: *mut LeanObject = *_args.add(12);
    let mut v___y_4476_: *mut LeanObject = *_args.add(13);
    let mut v___y_4477_: *mut LeanObject = *_args.add(14);
    let mut v___y_4478_: *mut LeanObject = *_args.add(15);
    let mut v___y_4479_: *mut LeanObject = *_args.add(16);
    let mut v_res_4480_: *mut LeanObject = core::ptr::null_mut();
    v_res_4480_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(
            v_upperBound_4463_,
            v_fvars_4464_,
            v_ids_4465_,
            v_inst_4466_,
            v_R_4467_,
            v_a_4468_,
            v_b_4469_,
            v_c_4470_,
            v___y_4471_,
            v___y_4472_,
            v___y_4473_,
            v___y_4474_,
            v___y_4475_,
            v___y_4476_,
            v___y_4477_,
            v___y_4478_,
        );
    lean_dec(v___y_4478_);
    lean_dec_ref(v___y_4477_);
    lean_dec(v___y_4476_);
    lean_dec_ref(v___y_4475_);
    lean_dec(v___y_4474_);
    lean_dec_ref(v___y_4473_);
    lean_dec(v___y_4472_);
    lean_dec_ref(v___y_4471_);
    lean_dec_ref(v_ids_4465_);
    lean_dec_ref(v_fvars_4464_);
    lean_dec(v_upperBound_4463_);
    return v_res_4480_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(
    mut v_o_4481_: *mut LeanObject,
    mut v___y_4482_: *mut LeanObject,
    mut v___y_4483_: *mut LeanObject,
    mut v___y_4484_: *mut LeanObject,
    mut v___y_4485_: *mut LeanObject,
    mut v___y_4486_: *mut LeanObject,
    mut v___y_4487_: *mut LeanObject,
    mut v___y_4488_: *mut LeanObject,
    mut v___y_4489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    v___x_4491_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_4481_, v___y_4489_);
    return v___x_4491_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___boxed(
    mut v_o_4492_: *mut LeanObject,
    mut v___y_4493_: *mut LeanObject,
    mut v___y_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
    mut v___y_4496_: *mut LeanObject,
    mut v___y_4497_: *mut LeanObject,
    mut v___y_4498_: *mut LeanObject,
    mut v___y_4499_: *mut LeanObject,
    mut v___y_4500_: *mut LeanObject,
    mut v___y_4501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4502_: *mut LeanObject = core::ptr::null_mut();
    v_res_4502_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(v_o_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
    lean_dec(v___y_4500_);
    lean_dec_ref(v___y_4499_);
    lean_dec(v___y_4498_);
    lean_dec_ref(v___y_4497_);
    lean_dec(v___y_4496_);
    lean_dec_ref(v___y_4495_);
    lean_dec(v___y_4494_);
    lean_dec_ref(v___y_4493_);
    return v_res_4502_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(
    mut v_ref_4503_: *mut LeanObject,
    mut v_msgData_4504_: *mut LeanObject,
    mut v_severity_4505_: u8,
    mut v_isSilent_4506_: u8,
    mut v___y_4507_: *mut LeanObject,
    mut v___y_4508_: *mut LeanObject,
    mut v___y_4509_: *mut LeanObject,
    mut v___y_4510_: *mut LeanObject,
    mut v___y_4511_: *mut LeanObject,
    mut v___y_4512_: *mut LeanObject,
    mut v___y_4513_: *mut LeanObject,
    mut v___y_4514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    v___x_4516_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4503_, v_msgData_4504_, v_severity_4505_, v_isSilent_4506_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
    return v___x_4516_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___boxed(
    mut v_ref_4517_: *mut LeanObject,
    mut v_msgData_4518_: *mut LeanObject,
    mut v_severity_4519_: *mut LeanObject,
    mut v_isSilent_4520_: *mut LeanObject,
    mut v___y_4521_: *mut LeanObject,
    mut v___y_4522_: *mut LeanObject,
    mut v___y_4523_: *mut LeanObject,
    mut v___y_4524_: *mut LeanObject,
    mut v___y_4525_: *mut LeanObject,
    mut v___y_4526_: *mut LeanObject,
    mut v___y_4527_: *mut LeanObject,
    mut v___y_4528_: *mut LeanObject,
    mut v___y_4529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_4530_: u8 = 0;
    let mut v_isSilent_boxed_4531_: u8 = 0;
    let mut v_res_4532_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_4530_ = (lean_unbox(v_severity_4519_) as u8);
    v_isSilent_boxed_4531_ = (lean_unbox(v_isSilent_4520_) as u8);
    v_res_4532_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(v_ref_4517_, v_msgData_4518_, v_severity_boxed_4530_, v_isSilent_boxed_4531_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
    lean_dec(v___y_4528_);
    lean_dec_ref(v___y_4527_);
    lean_dec(v___y_4526_);
    lean_dec_ref(v___y_4525_);
    lean_dec(v___y_4524_);
    lean_dec_ref(v___y_4523_);
    lean_dec(v___y_4522_);
    lean_dec_ref(v___y_4521_);
    lean_dec(v_ref_4517_);
    return v_res_4532_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    v___x_4533_ = lean_box(0);
    v___x_4534_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
    v___x_4535_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4535_, 0, v___x_4534_);
    lean_ctor_set(v___x_4535_, 1, v___x_4533_);
    return v___x_4535_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    v___x_4537_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___closed__0);
    v___x_4538_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4538_, 0, v___x_4537_);
    return v___x_4538_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg___boxed(
    mut v___y_4539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4540_: *mut LeanObject = core::ptr::null_mut();
    v_res_4540_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
    return v_res_4540_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0(
    mut v_00_u03b1_4541_: *mut LeanObject,
    mut v___y_4542_: *mut LeanObject,
    mut v___y_4543_: *mut LeanObject,
    mut v___y_4544_: *mut LeanObject,
    mut v___y_4545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    v___x_4547_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
    return v___x_4547_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___boxed(
    mut v_00_u03b1_4548_: *mut LeanObject,
    mut v___y_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
    mut v___y_4552_: *mut LeanObject,
    mut v___y_4553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4554_: *mut LeanObject = core::ptr::null_mut();
    v_res_4554_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0(v_00_u03b1_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
    lean_dec(v___y_4552_);
    lean_dec_ref(v___y_4551_);
    lean_dec(v___y_4550_);
    lean_dec_ref(v___y_4549_);
    return v_res_4554_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(
    mut v_msg_4555_: *mut LeanObject,
    mut v___y_4556_: *mut LeanObject,
    mut v___y_4557_: *mut LeanObject,
    mut v___y_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4566_: u8 = 0;
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4561_ = lean_ctor_get(v___y_4558_, 5);
                v___x_4562_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
                v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
                v_isSharedCheck_4571_ = (!lean_is_exclusive(v___x_4562_)) as u8;
                if v_isSharedCheck_4571_ == 0 {
                    v___x_4565_ = v___x_4562_;
                    v_isShared_4566_ = v_isSharedCheck_4571_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4563_);
                    lean_dec(v___x_4562_);
                    v___x_4565_ = lean_box(0);
                    v_isShared_4566_ = v_isSharedCheck_4571_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4561_);
                v___x_4567_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4567_, 0, v_ref_4561_);
                lean_ctor_set(v___x_4567_, 1, v_a_4563_);
                if v_isShared_4566_ == 0 {
                    lean_ctor_set_tag(v___x_4565_, 1);
                    lean_ctor_set(v___x_4565_, 0, v___x_4567_);
                    v___x_4569_ = v___x_4565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
                    v___x_4569_ = v_reuseFailAlloc_4570_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4569_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg___boxed(
    mut v_msg_4572_: *mut LeanObject,
    mut v___y_4573_: *mut LeanObject,
    mut v___y_4574_: *mut LeanObject,
    mut v___y_4575_: *mut LeanObject,
    mut v___y_4576_: *mut LeanObject,
    mut v___y_4577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4578_: *mut LeanObject = core::ptr::null_mut();
    v_res_4578_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v_msg_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
    lean_dec(v___y_4576_);
    lean_dec_ref(v___y_4575_);
    lean_dec(v___y_4574_);
    lean_dec_ref(v___y_4573_);
    return v_res_4578_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    v___x_4581_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__1;
    v___x_4582_ = l_Lean_stringToMessageData(v___x_4581_);
    return v___x_4582_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0(
    mut v_ctor_4583_: *mut LeanObject,
    mut v_args_4584_: *mut LeanObject,
    mut v___y_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
    mut v___y_4587_: *mut LeanObject,
    mut v___y_4588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4638_: u8 = 0;
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: u8 = 0;
    let mut v___x_4641_: u8 = 0;
    let mut v___x_4642_: u8 = 0;
    let mut v___x_4643_: u8 = 0;
    let mut v___x_4644_: u8 = 0;
    let mut v___x_4645_: u8 = 0;
    let mut v___x_4646_: u8 = 0;
    let mut v___x_4647_: u8 = 0;
    let mut v___x_4648_: u8 = 0;
    let mut v___x_4649_: u8 = 0;
    let mut v___x_4650_: u8 = 0;
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4654_: u8 = 0;
    let mut v_a_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4658_: u8 = 0;
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_a_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4666_: u8 = 0;
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4670_: u8 = 0;
    let mut v_a_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4674_: u8 = 0;
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4678_: u8 = 0;
    let mut v_a_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4682_: u8 = 0;
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4686_: u8 = 0;
    let mut v_a_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4690_: u8 = 0;
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4694_: u8 = 0;
    let mut v_a_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4698_: u8 = 0;
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4702_: u8 = 0;
    let mut v_a_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4706_: u8 = 0;
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4710_: u8 = 0;
    let mut v_a_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4714_: u8 = 0;
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4718_: u8 = 0;
    let mut v_a_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4722_: u8 = 0;
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4726_: u8 = 0;
    let mut v_a_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4730_: u8 = 0;
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4734_: u8 = 0;
    let mut v_a_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4738_: u8 = 0;
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4742_: u8 = 0;
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: u8 = 0;
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: u8 = 0;
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4754_: u8 = 0;
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4758_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4743_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0;
                v___x_4744_ = lean_string_dec_eq(v_ctor_4583_, v___x_4743_);
                if v___x_4744_ == 0 {
                    v___x_4745_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
                    return v___x_4745_;
                } else {
                    v___x_4746_ = lean_array_get_size(v_args_4584_);
                    v___x_4747_ = lean_unsigned_to_nat(11);
                    v___x_4748_ = lean_nat_dec_eq(v___x_4746_, v___x_4747_);
                    if v___x_4748_ == 0 {
                        v___x_4749_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2);
                        v___x_4750_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v___x_4749_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
                        v_a_4751_ = lean_ctor_get(v___x_4750_, 0);
                        v_isSharedCheck_4758_ = (!lean_is_exclusive(v___x_4750_)) as u8;
                        if v_isSharedCheck_4758_ == 0 {
                            v___x_4753_ = v___x_4750_;
                            v_isShared_4754_ = v_isSharedCheck_4758_;
                            state = 26;
                            continue;
                        } else {
                            lean_inc(v_a_4751_);
                            lean_dec(v___x_4750_);
                            v___x_4753_ = lean_box(0);
                            v_isShared_4754_ = v_isSharedCheck_4758_;
                            state = 26;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4591_ = l_Lean_instInhabitedExpr;
                v___x_4592_ = lean_unsigned_to_nat(0);
                v___x_4593_ = lean_array_get_borrowed(v___x_4591_, v_args_4584_, v___x_4592_);
                lean_inc(v___x_4593_);
                v___x_4594_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                    v___x_4593_,
                    v___y_4585_,
                    v___y_4586_,
                    v___y_4587_,
                    v___y_4588_,
                );
                if lean_obj_tag(v___x_4594_) == 0 {
                    v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
                    lean_inc(v_a_4595_);
                    lean_dec_ref_known(v___x_4594_, 1);
                    v___x_4596_ = lean_unsigned_to_nat(1);
                    v___x_4597_ = lean_array_get_borrowed(v___x_4591_, v_args_4584_, v___x_4596_);
                    lean_inc(v___x_4597_);
                    v___x_4598_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                        v___x_4597_,
                        v___y_4585_,
                        v___y_4586_,
                        v___y_4587_,
                        v___y_4588_,
                    );
                    if lean_obj_tag(v___x_4598_) == 0 {
                        v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
                        lean_inc(v_a_4599_);
                        lean_dec_ref_known(v___x_4598_, 1);
                        v___x_4600_ = lean_unsigned_to_nat(2);
                        v___x_4601_ =
                            lean_array_get_borrowed(v___x_4591_, v_args_4584_, v___x_4600_);
                        lean_inc(v___x_4601_);
                        v___x_4602_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                            v___x_4601_,
                            v___y_4585_,
                            v___y_4586_,
                            v___y_4587_,
                            v___y_4588_,
                        );
                        if lean_obj_tag(v___x_4602_) == 0 {
                            v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
                            lean_inc(v_a_4603_);
                            lean_dec_ref_known(v___x_4602_, 1);
                            v___x_4604_ = lean_unsigned_to_nat(3);
                            v___x_4605_ =
                                lean_array_get_borrowed(v___x_4591_, v_args_4584_, v___x_4604_);
                            lean_inc(v___x_4605_);
                            v___x_4606_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                                v___x_4605_,
                                v___y_4585_,
                                v___y_4586_,
                                v___y_4587_,
                                v___y_4588_,
                            );
                            if lean_obj_tag(v___x_4606_) == 0 {
                                v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
                                lean_inc(v_a_4607_);
                                lean_dec_ref_known(v___x_4606_, 1);
                                v___x_4608_ = lean_unsigned_to_nat(4);
                                v___x_4609_ =
                                    lean_array_get_borrowed(v___x_4591_, v_args_4584_, v___x_4608_);
                                lean_inc(v___x_4609_);
                                v___x_4610_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                                    v___x_4609_,
                                    v___y_4585_,
                                    v___y_4586_,
                                    v___y_4587_,
                                    v___y_4588_,
                                );
                                if lean_obj_tag(v___x_4610_) == 0 {
                                    v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
                                    lean_inc(v_a_4611_);
                                    lean_dec_ref_known(v___x_4610_, 1);
                                    v___x_4612_ = lean_unsigned_to_nat(5);
                                    v___x_4613_ = lean_array_get_borrowed(
                                        v___x_4591_,
                                        v_args_4584_,
                                        v___x_4612_,
                                    );
                                    lean_inc(v___x_4613_);
                                    v___x_4614_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                                        v___x_4613_,
                                        v___y_4585_,
                                        v___y_4586_,
                                        v___y_4587_,
                                        v___y_4588_,
                                    );
                                    if lean_obj_tag(v___x_4614_) == 0 {
                                        v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
                                        lean_inc(v_a_4615_);
                                        lean_dec_ref_known(v___x_4614_, 1);
                                        v___x_4616_ = lean_unsigned_to_nat(6);
                                        v___x_4617_ = lean_array_get_borrowed(
                                            v___x_4591_,
                                            v_args_4584_,
                                            v___x_4616_,
                                        );
                                        lean_inc(v___x_4617_);
                                        v___x_4618_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                                            v___x_4617_,
                                            v___y_4585_,
                                            v___y_4586_,
                                            v___y_4587_,
                                            v___y_4588_,
                                        );
                                        if lean_obj_tag(v___x_4618_) == 0 {
                                            v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
                                            lean_inc(v_a_4619_);
                                            lean_dec_ref_known(v___x_4618_, 1);
                                            v___x_4620_ = lean_unsigned_to_nat(7);
                                            v___x_4621_ = lean_array_get_borrowed(
                                                v___x_4591_,
                                                v_args_4584_,
                                                v___x_4620_,
                                            );
                                            lean_inc(v___x_4621_);
                                            v___x_4622_ =
                                                l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                                                    v___x_4621_,
                                                    v___y_4585_,
                                                    v___y_4586_,
                                                    v___y_4587_,
                                                    v___y_4588_,
                                                );
                                            if lean_obj_tag(v___x_4622_) == 0 {
                                                v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
                                                lean_inc(v_a_4623_);
                                                lean_dec_ref_known(v___x_4622_, 1);
                                                v___x_4624_ = lean_unsigned_to_nat(8);
                                                v___x_4625_ = lean_array_get_borrowed(
                                                    v___x_4591_,
                                                    v_args_4584_,
                                                    v___x_4624_,
                                                );
                                                lean_inc(v___x_4625_);
                                                v___x_4626_ =
                                                    l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                                                        v___x_4625_,
                                                        v___y_4585_,
                                                        v___y_4586_,
                                                        v___y_4587_,
                                                        v___y_4588_,
                                                    );
                                                if lean_obj_tag(v___x_4626_) == 0 {
                                                    v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
                                                    lean_inc(v_a_4627_);
                                                    lean_dec_ref_known(v___x_4626_, 1);
                                                    v___x_4628_ = lean_unsigned_to_nat(9);
                                                    v___x_4629_ = lean_array_get_borrowed(
                                                        v___x_4591_,
                                                        v_args_4584_,
                                                        v___x_4628_,
                                                    );
                                                    lean_inc(v___x_4629_);
                                                    v___x_4630_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_4629_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
                                                    if lean_obj_tag(v___x_4630_) == 0 {
                                                        v_a_4631_ = lean_ctor_get(v___x_4630_, 0);
                                                        lean_inc(v_a_4631_);
                                                        lean_dec_ref_known(v___x_4630_, 1);
                                                        v___x_4632_ = lean_unsigned_to_nat(10);
                                                        v___x_4633_ = lean_array_get_borrowed(
                                                            v___x_4591_,
                                                            v_args_4584_,
                                                            v___x_4632_,
                                                        );
                                                        lean_inc(v___x_4633_);
                                                        v___x_4634_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_4633_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
                                                        if lean_obj_tag(v___x_4634_) == 0 {
                                                            v_a_4635_ =
                                                                lean_ctor_get(v___x_4634_, 0);
                                                            v_isSharedCheck_4654_ =
                                                                (!lean_is_exclusive(v___x_4634_))
                                                                    as u8;
                                                            if v_isSharedCheck_4654_ == 0 {
                                                                v___x_4637_ = v___x_4634_;
                                                                v_isShared_4638_ =
                                                                    v_isSharedCheck_4654_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_4635_);
                                                                lean_dec(v___x_4634_);
                                                                v___x_4637_ = lean_box(0);
                                                                v_isShared_4638_ =
                                                                    v_isSharedCheck_4654_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec(v_a_4631_);
                                                            lean_dec(v_a_4627_);
                                                            lean_dec(v_a_4623_);
                                                            lean_dec(v_a_4619_);
                                                            lean_dec(v_a_4615_);
                                                            lean_dec(v_a_4611_);
                                                            lean_dec(v_a_4607_);
                                                            lean_dec(v_a_4603_);
                                                            lean_dec(v_a_4599_);
                                                            lean_dec(v_a_4595_);
                                                            v_a_4655_ =
                                                                lean_ctor_get(v___x_4634_, 0);
                                                            v_isSharedCheck_4662_ =
                                                                (!lean_is_exclusive(v___x_4634_))
                                                                    as u8;
                                                            if v_isSharedCheck_4662_ == 0 {
                                                                v___x_4657_ = v___x_4634_;
                                                                v_isShared_4658_ =
                                                                    v_isSharedCheck_4662_;
                                                                state = 4;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_4655_);
                                                                lean_dec(v___x_4634_);
                                                                v___x_4657_ = lean_box(0);
                                                                v_isShared_4658_ =
                                                                    v_isSharedCheck_4662_;
                                                                state = 4;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec(v_a_4627_);
                                                        lean_dec(v_a_4623_);
                                                        lean_dec(v_a_4619_);
                                                        lean_dec(v_a_4615_);
                                                        lean_dec(v_a_4611_);
                                                        lean_dec(v_a_4607_);
                                                        lean_dec(v_a_4603_);
                                                        lean_dec(v_a_4599_);
                                                        lean_dec(v_a_4595_);
                                                        v_a_4663_ = lean_ctor_get(v___x_4630_, 0);
                                                        v_isSharedCheck_4670_ =
                                                            (!lean_is_exclusive(v___x_4630_)) as u8;
                                                        if v_isSharedCheck_4670_ == 0 {
                                                            v___x_4665_ = v___x_4630_;
                                                            v_isShared_4666_ =
                                                                v_isSharedCheck_4670_;
                                                            state = 6;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_4663_);
                                                            lean_dec(v___x_4630_);
                                                            v___x_4665_ = lean_box(0);
                                                            v_isShared_4666_ =
                                                                v_isSharedCheck_4670_;
                                                            state = 6;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec(v_a_4623_);
                                                    lean_dec(v_a_4619_);
                                                    lean_dec(v_a_4615_);
                                                    lean_dec(v_a_4611_);
                                                    lean_dec(v_a_4607_);
                                                    lean_dec(v_a_4603_);
                                                    lean_dec(v_a_4599_);
                                                    lean_dec(v_a_4595_);
                                                    v_a_4671_ = lean_ctor_get(v___x_4626_, 0);
                                                    v_isSharedCheck_4678_ =
                                                        (!lean_is_exclusive(v___x_4626_)) as u8;
                                                    if v_isSharedCheck_4678_ == 0 {
                                                        v___x_4673_ = v___x_4626_;
                                                        v_isShared_4674_ = v_isSharedCheck_4678_;
                                                        state = 8;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_4671_);
                                                        lean_dec(v___x_4626_);
                                                        v___x_4673_ = lean_box(0);
                                                        v_isShared_4674_ = v_isSharedCheck_4678_;
                                                        state = 8;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_a_4619_);
                                                lean_dec(v_a_4615_);
                                                lean_dec(v_a_4611_);
                                                lean_dec(v_a_4607_);
                                                lean_dec(v_a_4603_);
                                                lean_dec(v_a_4599_);
                                                lean_dec(v_a_4595_);
                                                v_a_4679_ = lean_ctor_get(v___x_4622_, 0);
                                                v_isSharedCheck_4686_ =
                                                    (!lean_is_exclusive(v___x_4622_)) as u8;
                                                if v_isSharedCheck_4686_ == 0 {
                                                    v___x_4681_ = v___x_4622_;
                                                    v_isShared_4682_ = v_isSharedCheck_4686_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_4679_);
                                                    lean_dec(v___x_4622_);
                                                    v___x_4681_ = lean_box(0);
                                                    v_isShared_4682_ = v_isSharedCheck_4686_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_4615_);
                                            lean_dec(v_a_4611_);
                                            lean_dec(v_a_4607_);
                                            lean_dec(v_a_4603_);
                                            lean_dec(v_a_4599_);
                                            lean_dec(v_a_4595_);
                                            v_a_4687_ = lean_ctor_get(v___x_4618_, 0);
                                            v_isSharedCheck_4694_ =
                                                (!lean_is_exclusive(v___x_4618_)) as u8;
                                            if v_isSharedCheck_4694_ == 0 {
                                                v___x_4689_ = v___x_4618_;
                                                v_isShared_4690_ = v_isSharedCheck_4694_;
                                                state = 12;
                                                continue;
                                            } else {
                                                lean_inc(v_a_4687_);
                                                lean_dec(v___x_4618_);
                                                v___x_4689_ = lean_box(0);
                                                v_isShared_4690_ = v_isSharedCheck_4694_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_4611_);
                                        lean_dec(v_a_4607_);
                                        lean_dec(v_a_4603_);
                                        lean_dec(v_a_4599_);
                                        lean_dec(v_a_4595_);
                                        v_a_4695_ = lean_ctor_get(v___x_4614_, 0);
                                        v_isSharedCheck_4702_ =
                                            (!lean_is_exclusive(v___x_4614_)) as u8;
                                        if v_isSharedCheck_4702_ == 0 {
                                            v___x_4697_ = v___x_4614_;
                                            v_isShared_4698_ = v_isSharedCheck_4702_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4695_);
                                            lean_dec(v___x_4614_);
                                            v___x_4697_ = lean_box(0);
                                            v_isShared_4698_ = v_isSharedCheck_4702_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_4607_);
                                    lean_dec(v_a_4603_);
                                    lean_dec(v_a_4599_);
                                    lean_dec(v_a_4595_);
                                    v_a_4703_ = lean_ctor_get(v___x_4610_, 0);
                                    v_isSharedCheck_4710_ = (!lean_is_exclusive(v___x_4610_)) as u8;
                                    if v_isSharedCheck_4710_ == 0 {
                                        v___x_4705_ = v___x_4610_;
                                        v_isShared_4706_ = v_isSharedCheck_4710_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4703_);
                                        lean_dec(v___x_4610_);
                                        v___x_4705_ = lean_box(0);
                                        v_isShared_4706_ = v_isSharedCheck_4710_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_4603_);
                                lean_dec(v_a_4599_);
                                lean_dec(v_a_4595_);
                                v_a_4711_ = lean_ctor_get(v___x_4606_, 0);
                                v_isSharedCheck_4718_ = (!lean_is_exclusive(v___x_4606_)) as u8;
                                if v_isSharedCheck_4718_ == 0 {
                                    v___x_4713_ = v___x_4606_;
                                    v_isShared_4714_ = v_isSharedCheck_4718_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_a_4711_);
                                    lean_dec(v___x_4606_);
                                    v___x_4713_ = lean_box(0);
                                    v_isShared_4714_ = v_isSharedCheck_4718_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_4599_);
                            lean_dec(v_a_4595_);
                            v_a_4719_ = lean_ctor_get(v___x_4602_, 0);
                            v_isSharedCheck_4726_ = (!lean_is_exclusive(v___x_4602_)) as u8;
                            if v_isSharedCheck_4726_ == 0 {
                                v___x_4721_ = v___x_4602_;
                                v_isShared_4722_ = v_isSharedCheck_4726_;
                                state = 20;
                                continue;
                            } else {
                                lean_inc(v_a_4719_);
                                lean_dec(v___x_4602_);
                                v___x_4721_ = lean_box(0);
                                v_isShared_4722_ = v_isSharedCheck_4726_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4595_);
                        v_a_4727_ = lean_ctor_get(v___x_4598_, 0);
                        v_isSharedCheck_4734_ = (!lean_is_exclusive(v___x_4598_)) as u8;
                        if v_isSharedCheck_4734_ == 0 {
                            v___x_4729_ = v___x_4598_;
                            v_isShared_4730_ = v_isSharedCheck_4734_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_4727_);
                            lean_dec(v___x_4598_);
                            v___x_4729_ = lean_box(0);
                            v_isShared_4730_ = v_isSharedCheck_4734_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    v_a_4735_ = lean_ctor_get(v___x_4594_, 0);
                    v_isSharedCheck_4742_ = (!lean_is_exclusive(v___x_4594_)) as u8;
                    if v_isSharedCheck_4742_ == 0 {
                        v___x_4737_ = v___x_4594_;
                        v_isShared_4738_ = v_isSharedCheck_4742_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_4735_);
                        lean_dec(v___x_4594_);
                        v___x_4737_ = lean_box(0);
                        v_isShared_4738_ = v_isSharedCheck_4742_;
                        state = 24;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4639_ = lean_alloc_ctor(0, 0, (11) as u32);
                v___x_4640_ = (lean_unbox(v_a_4595_) as u8);
                lean_dec(v_a_4595_);
                lean_ctor_set_uint8(v___x_4639_, 0 as u32, v___x_4640_);
                v___x_4641_ = (lean_unbox(v_a_4599_) as u8);
                lean_dec(v_a_4599_);
                lean_ctor_set_uint8(v___x_4639_, 1 as u32, v___x_4641_);
                v___x_4642_ = (lean_unbox(v_a_4603_) as u8);
                lean_dec(v_a_4603_);
                lean_ctor_set_uint8(v___x_4639_, 2 as u32, v___x_4642_);
                v___x_4643_ = (lean_unbox(v_a_4607_) as u8);
                lean_dec(v_a_4607_);
                lean_ctor_set_uint8(v___x_4639_, 3 as u32, v___x_4643_);
                v___x_4644_ = (lean_unbox(v_a_4611_) as u8);
                lean_dec(v_a_4611_);
                lean_ctor_set_uint8(v___x_4639_, 4 as u32, v___x_4644_);
                v___x_4645_ = (lean_unbox(v_a_4615_) as u8);
                lean_dec(v_a_4615_);
                lean_ctor_set_uint8(v___x_4639_, 5 as u32, v___x_4645_);
                v___x_4646_ = (lean_unbox(v_a_4619_) as u8);
                lean_dec(v_a_4619_);
                lean_ctor_set_uint8(v___x_4639_, 6 as u32, v___x_4646_);
                v___x_4647_ = (lean_unbox(v_a_4623_) as u8);
                lean_dec(v_a_4623_);
                lean_ctor_set_uint8(v___x_4639_, 7 as u32, v___x_4647_);
                v___x_4648_ = (lean_unbox(v_a_4627_) as u8);
                lean_dec(v_a_4627_);
                lean_ctor_set_uint8(v___x_4639_, 8 as u32, v___x_4648_);
                v___x_4649_ = (lean_unbox(v_a_4631_) as u8);
                lean_dec(v_a_4631_);
                lean_ctor_set_uint8(v___x_4639_, 9 as u32, v___x_4649_);
                v___x_4650_ = (lean_unbox(v_a_4635_) as u8);
                lean_dec(v_a_4635_);
                lean_ctor_set_uint8(v___x_4639_, 10 as u32, v___x_4650_);
                if v_isShared_4638_ == 0 {
                    lean_ctor_set(v___x_4637_, 0, v___x_4639_);
                    v___x_4652_ = v___x_4637_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4653_, 0, v___x_4639_);
                    v___x_4652_ = v_reuseFailAlloc_4653_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4652_;
            }
            4 => {
                if v_isShared_4658_ == 0 {
                    v___x_4660_ = v___x_4657_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
                    v___x_4660_ = v_reuseFailAlloc_4661_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4660_;
            }
            6 => {
                if v_isShared_4666_ == 0 {
                    v___x_4668_ = v___x_4665_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
                    v___x_4668_ = v_reuseFailAlloc_4669_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4668_;
            }
            8 => {
                if v_isShared_4674_ == 0 {
                    v___x_4676_ = v___x_4673_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
                    v___x_4676_ = v_reuseFailAlloc_4677_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4676_;
            }
            10 => {
                if v_isShared_4682_ == 0 {
                    v___x_4684_ = v___x_4681_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
                    v___x_4684_ = v_reuseFailAlloc_4685_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4684_;
            }
            12 => {
                if v_isShared_4690_ == 0 {
                    v___x_4692_ = v___x_4689_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
                    v___x_4692_ = v_reuseFailAlloc_4693_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4692_;
            }
            14 => {
                if v_isShared_4698_ == 0 {
                    v___x_4700_ = v___x_4697_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4695_);
                    v___x_4700_ = v_reuseFailAlloc_4701_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4700_;
            }
            16 => {
                if v_isShared_4706_ == 0 {
                    v___x_4708_ = v___x_4705_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
                    v___x_4708_ = v_reuseFailAlloc_4709_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4708_;
            }
            18 => {
                if v_isShared_4714_ == 0 {
                    v___x_4716_ = v___x_4713_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4711_);
                    v___x_4716_ = v_reuseFailAlloc_4717_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4716_;
            }
            20 => {
                if v_isShared_4722_ == 0 {
                    v___x_4724_ = v___x_4721_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4725_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4719_);
                    v___x_4724_ = v_reuseFailAlloc_4725_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4724_;
            }
            22 => {
                if v_isShared_4730_ == 0 {
                    v___x_4732_ = v___x_4729_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4733_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4727_);
                    v___x_4732_ = v_reuseFailAlloc_4733_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4732_;
            }
            24 => {
                if v_isShared_4738_ == 0 {
                    v___x_4740_ = v___x_4737_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4741_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
                    v___x_4740_ = v_reuseFailAlloc_4741_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4740_;
            }
            26 => {
                if v_isShared_4754_ == 0 {
                    v___x_4756_ = v___x_4753_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4757_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4751_);
                    v___x_4756_ = v_reuseFailAlloc_4757_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___boxed(
    mut v_ctor_4759_: *mut LeanObject,
    mut v_args_4760_: *mut LeanObject,
    mut v___y_4761_: *mut LeanObject,
    mut v___y_4762_: *mut LeanObject,
    mut v___y_4763_: *mut LeanObject,
    mut v___y_4764_: *mut LeanObject,
    mut v___y_4765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4766_: *mut LeanObject = core::ptr::null_mut();
    v_res_4766_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0(v_ctor_4759_, v_args_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
    lean_dec(v___y_4764_);
    lean_dec_ref(v___y_4763_);
    lean_dec(v___y_4762_);
    lean_dec_ref(v___y_4761_);
    lean_dec_ref(v_args_4760_);
    lean_dec_ref(v_ctor_4759_);
    return v_res_4766_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(
    mut v_a_4774_: *mut LeanObject,
    mut v_a_4775_: *mut LeanObject,
    mut v_a_4776_: *mut LeanObject,
    mut v_a_4777_: *mut LeanObject,
    mut v_a_4778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    v___f_4780_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__0;
    v___x_4781_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3;
    v___x_4782_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
        v___x_4781_,
        v___f_4780_,
        v_a_4774_,
        v_a_4775_,
        v_a_4776_,
        v_a_4777_,
        v_a_4778_,
    );
    return v___x_4782_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___boxed(
    mut v_a_4783_: *mut LeanObject,
    mut v_a_4784_: *mut LeanObject,
    mut v_a_4785_: *mut LeanObject,
    mut v_a_4786_: *mut LeanObject,
    mut v_a_4787_: *mut LeanObject,
    mut v_a_4788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4789_: *mut LeanObject = core::ptr::null_mut();
    v_res_4789_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_);
    lean_dec(v_a_4787_);
    lean_dec_ref(v_a_4786_);
    lean_dec(v_a_4785_);
    lean_dec_ref(v_a_4784_);
    return v_res_4789_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1(
    mut v_00_u03b1_4790_: *mut LeanObject,
    mut v_msg_4791_: *mut LeanObject,
    mut v___y_4792_: *mut LeanObject,
    mut v___y_4793_: *mut LeanObject,
    mut v___y_4794_: *mut LeanObject,
    mut v___y_4795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    v___x_4797_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v_msg_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
    return v___x_4797_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___boxed(
    mut v_00_u03b1_4798_: *mut LeanObject,
    mut v_msg_4799_: *mut LeanObject,
    mut v___y_4800_: *mut LeanObject,
    mut v___y_4801_: *mut LeanObject,
    mut v___y_4802_: *mut LeanObject,
    mut v___y_4803_: *mut LeanObject,
    mut v___y_4804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4805_: *mut LeanObject = core::ptr::null_mut();
    v_res_4805_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1(v_00_u03b1_4798_, v_msg_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_);
    lean_dec(v___y_4803_);
    lean_dec_ref(v___y_4802_);
    lean_dec(v___y_4801_);
    lean_dec_ref(v___y_4800_);
    return v_res_4805_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1()
-> *mut LeanObject {
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    v___x_4807_ = lean_box(0);
    v___x_4808_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3;
    v___x_4809_ = l_Lean_Expr_const___override(v___x_4808_, v___x_4807_);
    return v___x_4809_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2()
-> *mut LeanObject {
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    v___x_4810_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1);
    v___x_4811_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4811_, 0, v___x_4810_);
    return v___x_4811_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3()
-> *mut LeanObject {
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    v___x_4812_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2);
    v___x_4813_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__0;
    v___x_4814_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4814_, 0, v___x_4813_);
    lean_ctor_set(v___x_4814_, 1, v___x_4812_);
    return v___x_4814_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig()
-> *mut LeanObject {
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    v___x_4815_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3_once), _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__3);
    return v___x_4815_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(
    mut v_e_4816_: *mut LeanObject,
    mut v___y_4817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4819_: u8 = 0;
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4833_: u8 = 0;
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4839_: u8 = 0;
    let mut v_unused_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4819_ = l_Lean_Expr_hasMVar(v_e_4816_);
                if v___x_4819_ == 0 {
                    v___x_4820_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4820_, 0, v_e_4816_);
                    return v___x_4820_;
                } else {
                    v___x_4821_ = lean_st_ref_get(v___y_4817_);
                    v_mctx_4822_ = lean_ctor_get(v___x_4821_, 0);
                    lean_inc_ref(v_mctx_4822_);
                    lean_dec(v___x_4821_);
                    v___x_4823_ = l_Lean_instantiateMVarsCore(v_mctx_4822_, v_e_4816_);
                    v_fst_4824_ = lean_ctor_get(v___x_4823_, 0);
                    lean_inc(v_fst_4824_);
                    v_snd_4825_ = lean_ctor_get(v___x_4823_, 1);
                    lean_inc(v_snd_4825_);
                    lean_dec_ref(v___x_4823_);
                    v___x_4826_ = lean_st_ref_take(v___y_4817_);
                    v_cache_4827_ = lean_ctor_get(v___x_4826_, 1);
                    v_zetaDeltaFVarIds_4828_ = lean_ctor_get(v___x_4826_, 2);
                    v_postponed_4829_ = lean_ctor_get(v___x_4826_, 3);
                    v_diag_4830_ = lean_ctor_get(v___x_4826_, 4);
                    v_isSharedCheck_4839_ = (!lean_is_exclusive(v___x_4826_)) as u8;
                    if v_isSharedCheck_4839_ == 0 {
                        v_unused_4840_ = lean_ctor_get(v___x_4826_, 0);
                        lean_dec(v_unused_4840_);
                        v___x_4832_ = v___x_4826_;
                        v_isShared_4833_ = v_isSharedCheck_4839_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_4830_);
                        lean_inc(v_postponed_4829_);
                        lean_inc(v_zetaDeltaFVarIds_4828_);
                        lean_inc(v_cache_4827_);
                        lean_dec(v___x_4826_);
                        v___x_4832_ = lean_box(0);
                        v_isShared_4833_ = v_isSharedCheck_4839_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4833_ == 0 {
                    lean_ctor_set(v___x_4832_, 0, v_snd_4825_);
                    v___x_4835_ = v___x_4832_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4838_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_snd_4825_);
                    lean_ctor_set(v_reuseFailAlloc_4838_, 1, v_cache_4827_);
                    lean_ctor_set(v_reuseFailAlloc_4838_, 2, v_zetaDeltaFVarIds_4828_);
                    lean_ctor_set(v_reuseFailAlloc_4838_, 3, v_postponed_4829_);
                    lean_ctor_set(v_reuseFailAlloc_4838_, 4, v_diag_4830_);
                    v___x_4835_ = v_reuseFailAlloc_4838_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4836_ = lean_st_ref_set(v___y_4817_, v___x_4835_);
                v___x_4837_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4837_, 0, v_fst_4824_);
                return v___x_4837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(
    mut v_e_4841_: *mut LeanObject,
    mut v___y_4842_: *mut LeanObject,
    mut v___y_4843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4844_: *mut LeanObject = core::ptr::null_mut();
    v_res_4844_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_4841_, v___y_4842_);
    lean_dec(v___y_4842_);
    return v_res_4844_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    v___x_4845_ = lean_box(1);
    v___x_4846_ = l_Lean_MessageData_ofFormat(v___x_4845_);
    return v___x_4846_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    v___x_4850_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__2;
    v___x_4851_ = l_Lean_MessageData_ofFormat(v___x_4850_);
    return v___x_4851_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(
    mut v_x_4852_: *mut LeanObject,
    mut v_x_4853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4858_: u8 = 0;
    let mut v_before_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4862_: u8 = 0;
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4875_: u8 = 0;
    let mut v_unused_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4853_) == 0 {
                    return v_x_4852_;
                } else {
                    v_head_4854_ = lean_ctor_get(v_x_4853_, 0);
                    v_tail_4855_ = lean_ctor_get(v_x_4853_, 1);
                    v_isSharedCheck_4877_ = (!lean_is_exclusive(v_x_4853_)) as u8;
                    if v_isSharedCheck_4877_ == 0 {
                        v___x_4857_ = v_x_4853_;
                        v_isShared_4858_ = v_isSharedCheck_4877_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4855_);
                        lean_inc(v_head_4854_);
                        lean_dec(v_x_4853_);
                        v___x_4857_ = lean_box(0);
                        v_isShared_4858_ = v_isSharedCheck_4877_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_4859_ = lean_ctor_get(v_head_4854_, 0);
                v_isSharedCheck_4875_ = (!lean_is_exclusive(v_head_4854_)) as u8;
                if v_isSharedCheck_4875_ == 0 {
                    v_unused_4876_ = lean_ctor_get(v_head_4854_, 1);
                    lean_dec(v_unused_4876_);
                    v___x_4861_ = v_head_4854_;
                    v_isShared_4862_ = v_isSharedCheck_4875_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_4859_);
                    lean_dec(v_head_4854_);
                    v___x_4861_ = lean_box(0);
                    v_isShared_4862_ = v_isSharedCheck_4875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4863_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0);
                if v_isShared_4862_ == 0 {
                    lean_ctor_set_tag(v___x_4861_, 7);
                    lean_ctor_set(v___x_4861_, 1, v___x_4863_);
                    lean_ctor_set(v___x_4861_, 0, v_x_4852_);
                    v___x_4865_ = v___x_4861_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4874_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_x_4852_);
                    lean_ctor_set(v_reuseFailAlloc_4874_, 1, v___x_4863_);
                    v___x_4865_ = v_reuseFailAlloc_4874_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4866_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__3);
                if v_isShared_4858_ == 0 {
                    lean_ctor_set_tag(v___x_4857_, 7);
                    lean_ctor_set(v___x_4857_, 1, v___x_4866_);
                    lean_ctor_set(v___x_4857_, 0, v___x_4865_);
                    v___x_4868_ = v___x_4857_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4873_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4873_, 0, v___x_4865_);
                    lean_ctor_set(v_reuseFailAlloc_4873_, 1, v___x_4866_);
                    v___x_4868_ = v_reuseFailAlloc_4873_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4869_ = l_Lean_MessageData_ofSyntax(v_before_4859_);
                v___x_4870_ = l_Lean_indentD(v___x_4869_);
                v___x_4871_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4871_, 0, v___x_4868_);
                lean_ctor_set(v___x_4871_, 1, v___x_4870_);
                v_x_4852_ = v___x_4871_;
                v_x_4853_ = v_tail_4855_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    v___x_4881_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1;
    v___x_4882_ = l_Lean_MessageData_ofFormat(v___x_4881_);
    return v___x_4882_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(
    mut v_msgData_4883_: *mut LeanObject,
    mut v_macroStack_4884_: *mut LeanObject,
    mut v___y_4885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: u8 = 0;
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4896_: u8 = 0;
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4908_: u8 = 0;
    let mut v_unused_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4887_ = lean_ctor_get(v___y_4885_, 2);
                v___x_4888_ = l_Lean_Elab_pp_macroStack;
                v___x_4889_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_options_4887_, v___x_4888_);
                if v___x_4889_ == 0 {
                    lean_dec(v_macroStack_4884_);
                    v___x_4890_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4890_, 0, v_msgData_4883_);
                    return v___x_4890_;
                } else {
                    if lean_obj_tag(v_macroStack_4884_) == 0 {
                        v___x_4891_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4891_, 0, v_msgData_4883_);
                        return v___x_4891_;
                    } else {
                        v_head_4892_ = lean_ctor_get(v_macroStack_4884_, 0);
                        lean_inc(v_head_4892_);
                        v_after_4893_ = lean_ctor_get(v_head_4892_, 1);
                        v_isSharedCheck_4908_ = (!lean_is_exclusive(v_head_4892_)) as u8;
                        if v_isSharedCheck_4908_ == 0 {
                            v_unused_4909_ = lean_ctor_get(v_head_4892_, 0);
                            lean_dec(v_unused_4909_);
                            v___x_4895_ = v_head_4892_;
                            v_isShared_4896_ = v_isSharedCheck_4908_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_4893_);
                            lean_dec(v_head_4892_);
                            v___x_4895_ = lean_box(0);
                            v_isShared_4896_ = v_isSharedCheck_4908_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4897_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___closed__0);
                if v_isShared_4896_ == 0 {
                    lean_ctor_set_tag(v___x_4895_, 7);
                    lean_ctor_set(v___x_4895_, 1, v___x_4897_);
                    lean_ctor_set(v___x_4895_, 0, v_msgData_4883_);
                    v___x_4899_ = v___x_4895_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4907_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_msgData_4883_);
                    lean_ctor_set(v_reuseFailAlloc_4907_, 1, v___x_4897_);
                    v___x_4899_ = v_reuseFailAlloc_4907_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4900_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
                v___x_4901_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4901_, 0, v___x_4899_);
                lean_ctor_set(v___x_4901_, 1, v___x_4900_);
                v___x_4902_ = l_Lean_MessageData_ofSyntax(v_after_4893_);
                v___x_4903_ = l_Lean_indentD(v___x_4902_);
                v_msgData_4904_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_4904_, 0, v___x_4901_);
                lean_ctor_set(v_msgData_4904_, 1, v___x_4903_);
                v___x_4905_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_msgData_4904_, v_macroStack_4884_);
                v___x_4906_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4906_, 0, v___x_4905_);
                return v___x_4906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_msgData_4910_: *mut LeanObject,
    mut v_macroStack_4911_: *mut LeanObject,
    mut v___y_4912_: *mut LeanObject,
    mut v___y_4913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4914_: *mut LeanObject = core::ptr::null_mut();
    v_res_4914_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_4910_, v_macroStack_4911_, v___y_4912_);
    lean_dec_ref(v___y_4912_);
    return v_res_4914_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(
    mut v_msg_4915_: *mut LeanObject,
    mut v___y_4916_: *mut LeanObject,
    mut v___y_4917_: *mut LeanObject,
    mut v___y_4918_: *mut LeanObject,
    mut v___y_4919_: *mut LeanObject,
    mut v___y_4920_: *mut LeanObject,
    mut v___y_4921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4932_: u8 = 0;
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4923_ = lean_ctor_get(v___y_4920_, 5);
                v___x_4924_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_4915_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_);
                v_a_4925_ = lean_ctor_get(v___x_4924_, 0);
                lean_inc(v_a_4925_);
                lean_dec_ref(v___x_4924_);
                v_macroStack_4926_ = lean_ctor_get(v___y_4916_, 1);
                v___x_4927_ = l_Lean_Elab_getBetterRef(v_ref_4923_, v_macroStack_4926_);
                lean_inc(v_macroStack_4926_);
                v___x_4928_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_4925_, v_macroStack_4926_, v___y_4920_);
                v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
                v_isSharedCheck_4937_ = (!lean_is_exclusive(v___x_4928_)) as u8;
                if v_isSharedCheck_4937_ == 0 {
                    v___x_4931_ = v___x_4928_;
                    v_isShared_4932_ = v_isSharedCheck_4937_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4929_);
                    lean_dec(v___x_4928_);
                    v___x_4931_ = lean_box(0);
                    v_isShared_4932_ = v_isSharedCheck_4937_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4933_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4933_, 0, v___x_4927_);
                lean_ctor_set(v___x_4933_, 1, v_a_4929_);
                if v_isShared_4932_ == 0 {
                    lean_ctor_set_tag(v___x_4931_, 1);
                    lean_ctor_set(v___x_4931_, 0, v___x_4933_);
                    v___x_4935_ = v___x_4931_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4933_);
                    v___x_4935_ = v_reuseFailAlloc_4936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4935_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(
    mut v_msg_4938_: *mut LeanObject,
    mut v___y_4939_: *mut LeanObject,
    mut v___y_4940_: *mut LeanObject,
    mut v___y_4941_: *mut LeanObject,
    mut v___y_4942_: *mut LeanObject,
    mut v___y_4943_: *mut LeanObject,
    mut v___y_4944_: *mut LeanObject,
    mut v___y_4945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4946_: *mut LeanObject = core::ptr::null_mut();
    v_res_4946_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_);
    lean_dec(v___y_4944_);
    lean_dec_ref(v___y_4943_);
    lean_dec(v___y_4942_);
    lean_dec_ref(v___y_4941_);
    lean_dec(v___y_4940_);
    lean_dec_ref(v___y_4939_);
    return v_res_4946_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    v___x_4947_ = lean_box(0);
    v___x_4948_ = l_Lean_Elab_abortTermExceptionId;
    v___x_4949_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4949_, 0, v___x_4948_);
    lean_ctor_set(v___x_4949_, 1, v___x_4947_);
    return v___x_4949_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg()
-> *mut LeanObject {
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    v___x_4951_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
    v___x_4952_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4952_, 0, v___x_4951_);
    return v___x_4952_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(
    mut v___y_4953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4954_: *mut LeanObject = core::ptr::null_mut();
    v_res_4954_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
    return v_res_4954_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    v___x_4956_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__0;
    v___x_4957_ = l_Lean_stringToMessageData(v___x_4956_);
    return v___x_4957_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    v___x_4958_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__1);
    v___x_4959_ = l_Lean_MessageData_ofExpr(v___x_4958_);
    return v___x_4959_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    v___x_4960_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__2);
    v___x_4961_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1);
    v___x_4962_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4962_, 0, v___x_4961_);
    lean_ctor_set(v___x_4962_, 1, v___x_4960_);
    return v___x_4962_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    v___x_4964_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__4;
    v___x_4965_ = l_Lean_stringToMessageData(v___x_4964_);
    return v___x_4965_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6()
-> *mut LeanObject {
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
    v___x_4966_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5);
    v___x_4967_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__3);
    v___x_4968_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4968_, 0, v___x_4967_);
    lean_ctor_set(v___x_4968_, 1, v___x_4966_);
    return v___x_4968_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8()
-> *mut LeanObject {
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    v___x_4970_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__7;
    v___x_4971_ = l_Lean_stringToMessageData(v___x_4970_);
    return v___x_4971_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10()
-> *mut LeanObject {
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    v___x_4973_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__9;
    v___x_4974_ = l_Lean_stringToMessageData(v___x_4973_);
    return v___x_4974_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(
    mut v_stx_4975_: *mut LeanObject,
    mut v_a_4976_: *mut LeanObject,
    mut v_a_4977_: *mut LeanObject,
    mut v_a_4978_: *mut LeanObject,
    mut v_a_4979_: *mut LeanObject,
    mut v_a_4980_: *mut LeanObject,
    mut v_a_4981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ty_x3f_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: u8 = 0;
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5001_: u8 = 0;
    let mut v_cancelTk_x3f_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5003_: u8 = 0;
    let mut v_inheritedTraceOptions_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: u8 = 0;
    let mut v_ref_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5022_: u8 = 0;
    let mut v_id_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5026_: u8 = 0;
    let mut v___x_5027_: u8 = 0;
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_unused_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: u8 = 0;
    let mut v___x_5049_: u8 = 0;
    let mut v___y_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: u8 = 0;
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5066_: u8 = 0;
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5070_: u8 = 0;
    let mut v_a_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5074_: u8 = 0;
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5078_: u8 = 0;
    let mut v_a_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5082_: u8 = 0;
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5086_: u8 = 0;
    let mut v___y_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5101_: u8 = 0;
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5105_: u8 = 0;
    let mut v___x_5106_: u8 = 0;
    let mut v___x_5107_: u8 = 0;
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5112_: u8 = 0;
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5116_: u8 = 0;
    let mut v_a_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5120_: u8 = 0;
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5124_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ty_x3f_4983_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig___closed__2);
                v___x_4984_ = 1;
                v___x_4985_ = lean_box(0);
                v___x_4986_ = lean_box((v___x_4984_) as usize);
                v___x_4987_ = lean_box((v___x_4984_) as usize);
                lean_inc(v_stx_4975_);
                v___x_4988_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___x_4988_, 0, v_stx_4975_);
                lean_closure_set(v___x_4988_, 1, v_ty_x3f_4983_);
                lean_closure_set(v___x_4988_, 2, v___x_4986_);
                lean_closure_set(v___x_4988_, 3, v___x_4987_);
                lean_closure_set(v___x_4988_, 4, v___x_4985_);
                v_fileName_4989_ = lean_ctor_get(v_a_4980_, 0);
                v_fileMap_4990_ = lean_ctor_get(v_a_4980_, 1);
                v_options_4991_ = lean_ctor_get(v_a_4980_, 2);
                v_currRecDepth_4992_ = lean_ctor_get(v_a_4980_, 3);
                v_maxRecDepth_4993_ = lean_ctor_get(v_a_4980_, 4);
                v_ref_4994_ = lean_ctor_get(v_a_4980_, 5);
                v_currNamespace_4995_ = lean_ctor_get(v_a_4980_, 6);
                v_openDecls_4996_ = lean_ctor_get(v_a_4980_, 7);
                v_initHeartbeats_4997_ = lean_ctor_get(v_a_4980_, 8);
                v_maxHeartbeats_4998_ = lean_ctor_get(v_a_4980_, 9);
                v_quotContext_4999_ = lean_ctor_get(v_a_4980_, 10);
                v_currMacroScope_5000_ = lean_ctor_get(v_a_4980_, 11);
                v_diag_5001_ = lean_ctor_get_uint8(
                    v_a_4980_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5002_ = lean_ctor_get(v_a_4980_, 12);
                v_suppressElabErrors_5003_ = lean_ctor_get_uint8(
                    v_a_4980_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5004_ = lean_ctor_get(v_a_4980_, 13);
                v___x_5005_ = 1;
                v_ref_5006_ = l_Lean_replaceRef(v_stx_4975_, v_ref_4994_);
                lean_dec(v_stx_4975_);
                lean_inc_ref(v_inheritedTraceOptions_5004_);
                lean_inc(v_cancelTk_x3f_5002_);
                lean_inc(v_currMacroScope_5000_);
                lean_inc(v_quotContext_4999_);
                lean_inc(v_maxHeartbeats_4998_);
                lean_inc(v_initHeartbeats_4997_);
                lean_inc(v_openDecls_4996_);
                lean_inc(v_currNamespace_4995_);
                lean_inc(v_maxRecDepth_4993_);
                lean_inc(v_currRecDepth_4992_);
                lean_inc_ref(v_options_4991_);
                lean_inc_ref(v_fileMap_4990_);
                lean_inc_ref(v_fileName_4989_);
                v___x_5007_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_5007_, 0, v_fileName_4989_);
                lean_ctor_set(v___x_5007_, 1, v_fileMap_4990_);
                lean_ctor_set(v___x_5007_, 2, v_options_4991_);
                lean_ctor_set(v___x_5007_, 3, v_currRecDepth_4992_);
                lean_ctor_set(v___x_5007_, 4, v_maxRecDepth_4993_);
                lean_ctor_set(v___x_5007_, 5, v_ref_5006_);
                lean_ctor_set(v___x_5007_, 6, v_currNamespace_4995_);
                lean_ctor_set(v___x_5007_, 7, v_openDecls_4996_);
                lean_ctor_set(v___x_5007_, 8, v_initHeartbeats_4997_);
                lean_ctor_set(v___x_5007_, 9, v_maxHeartbeats_4998_);
                lean_ctor_set(v___x_5007_, 10, v_quotContext_4999_);
                lean_ctor_set(v___x_5007_, 11, v_currMacroScope_5000_);
                lean_ctor_set(v___x_5007_, 12, v_cancelTk_x3f_5002_);
                lean_ctor_set(v___x_5007_, 13, v_inheritedTraceOptions_5004_);
                lean_ctor_set_uint8(
                    v___x_5007_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_5001_,
                );
                lean_ctor_set_uint8(
                    v___x_5007_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5003_,
                );
                v___x_5008_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_4988_,
                        v___x_5005_,
                        v_a_4976_,
                        v_a_4977_,
                        v_a_4978_,
                        v_a_4979_,
                        v___x_5007_,
                        v_a_4981_,
                    );
                if lean_obj_tag(v___x_5008_) == 0 {
                    v_a_5009_ = lean_ctor_get(v___x_5008_, 0);
                    lean_inc(v_a_5009_);
                    lean_dec_ref_known(v___x_5008_, 1);
                    v___x_5010_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_5009_, v_a_4979_);
                    v_a_5011_ = lean_ctor_get(v___x_5010_, 0);
                    lean_inc(v_a_5011_);
                    lean_dec_ref(v___x_5010_);
                    v___x_5106_ = l_Lean_Expr_hasSorry(v_a_5011_);
                    if v___x_5106_ == 0 {
                        v___y_5051_ = v_a_4976_;
                        v___y_5052_ = v_a_4977_;
                        v___y_5053_ = v_a_4978_;
                        v___y_5054_ = v_a_4979_;
                        v___y_5055_ = v___x_5007_;
                        v___y_5056_ = v_a_4981_;
                        state = 5;
                        continue;
                    } else {
                        v___x_5107_ = l_Lean_Expr_hasSyntheticSorry(v_a_5011_);
                        if v___x_5107_ == 0 {
                            v___y_5088_ = v_a_4976_;
                            v___y_5089_ = v_a_4977_;
                            v___y_5090_ = v_a_4978_;
                            v___y_5091_ = v_a_4979_;
                            v___y_5092_ = v___x_5007_;
                            v___y_5093_ = v_a_4981_;
                            state = 12;
                            continue;
                        } else {
                            lean_dec(v_a_5011_);
                            lean_dec_ref_known(v___x_5007_, 14);
                            v___x_5108_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
                            v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
                            v_isSharedCheck_5116_ = (!lean_is_exclusive(v___x_5108_)) as u8;
                            if v_isSharedCheck_5116_ == 0 {
                                v___x_5111_ = v___x_5108_;
                                v_isShared_5112_ = v_isSharedCheck_5116_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_5109_);
                                lean_dec(v___x_5108_);
                                v___x_5111_ = lean_box(0);
                                v_isShared_5112_ = v_isSharedCheck_5116_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_5007_, 14);
                    v_a_5117_ = lean_ctor_get(v___x_5008_, 0);
                    v_isSharedCheck_5124_ = (!lean_is_exclusive(v___x_5008_)) as u8;
                    if v_isSharedCheck_5124_ == 0 {
                        v___x_5119_ = v___x_5008_;
                        v_isShared_5120_ = v_isSharedCheck_5124_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_5117_);
                        lean_dec(v___x_5008_);
                        v___x_5119_ = lean_box(0);
                        v_isShared_5120_ = v_isSharedCheck_5124_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5022_ == 0 {
                    if lean_obj_tag(v___y_5013_) == 0 {
                        lean_dec_ref_known(v___y_5013_, 2);
                        lean_dec_ref(v___y_5021_);
                        lean_dec(v_a_5011_);
                        return v___y_5016_;
                    } else {
                        v_id_5023_ = lean_ctor_get(v___y_5013_, 0);
                        v_isSharedCheck_5036_ = (!lean_is_exclusive(v___y_5013_)) as u8;
                        if v_isSharedCheck_5036_ == 0 {
                            v_unused_5037_ = lean_ctor_get(v___y_5013_, 1);
                            lean_dec(v_unused_5037_);
                            v___x_5025_ = v___y_5013_;
                            v_isShared_5026_ = v_isSharedCheck_5036_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_id_5023_);
                            lean_dec(v___y_5013_);
                            v___x_5025_ = lean_box(0);
                            v_isShared_5026_ = v_isSharedCheck_5036_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_5021_);
                    lean_dec_ref(v___y_5013_);
                    lean_dec(v_a_5011_);
                    return v___y_5016_;
                }
            }
            2 => {
                v___x_5027_ = l_Lean_instBEqInternalExceptionId_beq(v___y_5020_, v_id_5023_);
                lean_dec(v_id_5023_);
                if v___x_5027_ == 0 {
                    lean_del_object(v___x_5025_);
                    lean_dec_ref(v___y_5021_);
                    lean_dec(v_a_5011_);
                    return v___y_5016_;
                } else {
                    lean_dec_ref(v___y_5016_);
                    v___x_5028_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__6);
                    v___x_5029_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8);
                    v___x_5030_ = l_Lean_indentExpr(v_a_5011_);
                    if v_isShared_5026_ == 0 {
                        lean_ctor_set_tag(v___x_5025_, 7);
                        lean_ctor_set(v___x_5025_, 1, v___x_5030_);
                        lean_ctor_set(v___x_5025_, 0, v___x_5029_);
                        v___x_5032_ = v___x_5025_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5035_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5035_, 0, v___x_5029_);
                        lean_ctor_set(v_reuseFailAlloc_5035_, 1, v___x_5030_);
                        v___x_5032_ = v_reuseFailAlloc_5035_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5033_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5033_, 0, v___x_5032_);
                lean_ctor_set(v___x_5033_, 1, v___x_5028_);
                v___x_5034_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_5033_, v___y_5014_, v___y_5018_, v___y_5017_, v___y_5015_, v___y_5021_, v___y_5019_);
                lean_dec_ref(v___y_5021_);
                return v___x_5034_;
            }
            4 => {
                lean_inc(v_a_5011_);
                v___x_5045_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v_a_5011_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
                if lean_obj_tag(v___x_5045_) == 0 {
                    lean_dec_ref(v___y_5043_);
                    lean_dec(v_a_5011_);
                    return v___x_5045_;
                } else {
                    v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
                    lean_inc(v_a_5046_);
                    v___x_5047_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_5048_ = l_Lean_Exception_isInterrupt(v_a_5046_);
                    if v___x_5048_ == 0 {
                        lean_inc(v_a_5046_);
                        v___x_5049_ = l_Lean_Exception_isRuntime(v_a_5046_);
                        v___y_5013_ = v_a_5046_;
                        v___y_5014_ = v___y_5039_;
                        v___y_5015_ = v___y_5042_;
                        v___y_5016_ = v___x_5045_;
                        v___y_5017_ = v___y_5041_;
                        v___y_5018_ = v___y_5040_;
                        v___y_5019_ = v___y_5044_;
                        v___y_5020_ = v___x_5047_;
                        v___y_5021_ = v___y_5043_;
                        v___y_5022_ = v___x_5049_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5013_ = v_a_5046_;
                        v___y_5014_ = v___y_5039_;
                        v___y_5015_ = v___y_5042_;
                        v___y_5016_ = v___x_5045_;
                        v___y_5017_ = v___y_5041_;
                        v___y_5018_ = v___y_5040_;
                        v___y_5019_ = v___y_5044_;
                        v___y_5020_ = v___x_5047_;
                        v___y_5021_ = v___y_5043_;
                        v___y_5022_ = v___x_5048_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_5011_);
                v___x_5057_ = l_Lean_Meta_getMVars(
                    v_a_5011_,
                    v___y_5053_,
                    v___y_5054_,
                    v___y_5055_,
                    v___y_5056_,
                );
                if lean_obj_tag(v___x_5057_) == 0 {
                    v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
                    lean_inc(v_a_5058_);
                    lean_dec_ref_known(v___x_5057_, 1);
                    v___x_5059_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                        v_a_5058_,
                        v___x_4985_,
                        v___y_5051_,
                        v___y_5052_,
                        v___y_5053_,
                        v___y_5054_,
                        v___y_5055_,
                        v___y_5056_,
                    );
                    lean_dec(v_a_5058_);
                    if lean_obj_tag(v___x_5059_) == 0 {
                        v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
                        lean_inc(v_a_5060_);
                        lean_dec_ref_known(v___x_5059_, 1);
                        v___x_5061_ = (lean_unbox(v_a_5060_) as u8);
                        lean_dec(v_a_5060_);
                        if v___x_5061_ == 0 {
                            v___y_5039_ = v___y_5051_;
                            v___y_5040_ = v___y_5052_;
                            v___y_5041_ = v___y_5053_;
                            v___y_5042_ = v___y_5054_;
                            v___y_5043_ = v___y_5055_;
                            v___y_5044_ = v___y_5056_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v___y_5055_);
                            lean_dec(v_a_5011_);
                            v___x_5062_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
                            v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
                            v_isSharedCheck_5070_ = (!lean_is_exclusive(v___x_5062_)) as u8;
                            if v_isSharedCheck_5070_ == 0 {
                                v___x_5065_ = v___x_5062_;
                                v_isShared_5066_ = v_isSharedCheck_5070_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_5063_);
                                lean_dec(v___x_5062_);
                                v___x_5065_ = lean_box(0);
                                v_isShared_5066_ = v_isSharedCheck_5070_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_5055_);
                        lean_dec(v_a_5011_);
                        v_a_5071_ = lean_ctor_get(v___x_5059_, 0);
                        v_isSharedCheck_5078_ = (!lean_is_exclusive(v___x_5059_)) as u8;
                        if v_isSharedCheck_5078_ == 0 {
                            v___x_5073_ = v___x_5059_;
                            v_isShared_5074_ = v_isSharedCheck_5078_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_5071_);
                            lean_dec(v___x_5059_);
                            v___x_5073_ = lean_box(0);
                            v_isShared_5074_ = v_isSharedCheck_5078_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_5055_);
                    lean_dec(v_a_5011_);
                    v_a_5079_ = lean_ctor_get(v___x_5057_, 0);
                    v_isSharedCheck_5086_ = (!lean_is_exclusive(v___x_5057_)) as u8;
                    if v_isSharedCheck_5086_ == 0 {
                        v___x_5081_ = v___x_5057_;
                        v_isShared_5082_ = v_isSharedCheck_5086_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5079_);
                        lean_dec(v___x_5057_);
                        v___x_5081_ = lean_box(0);
                        v_isShared_5082_ = v_isSharedCheck_5086_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5066_ == 0 {
                    v___x_5068_ = v___x_5065_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5069_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_a_5063_);
                    v___x_5068_ = v_reuseFailAlloc_5069_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5068_;
            }
            8 => {
                if v_isShared_5074_ == 0 {
                    v___x_5076_ = v___x_5073_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5077_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5071_);
                    v___x_5076_ = v_reuseFailAlloc_5077_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5076_;
            }
            10 => {
                if v_isShared_5082_ == 0 {
                    v___x_5084_ = v___x_5081_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
                    v___x_5084_ = v_reuseFailAlloc_5085_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5084_;
            }
            12 => {
                v___x_5094_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10);
                v___x_5095_ = l_Lean_indentExpr(v_a_5011_);
                v___x_5096_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5096_, 0, v___x_5094_);
                lean_ctor_set(v___x_5096_, 1, v___x_5095_);
                v___x_5097_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_5096_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_);
                lean_dec_ref(v___y_5092_);
                v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
                v_isSharedCheck_5105_ = (!lean_is_exclusive(v___x_5097_)) as u8;
                if v_isSharedCheck_5105_ == 0 {
                    v___x_5100_ = v___x_5097_;
                    v_isShared_5101_ = v_isSharedCheck_5105_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_a_5098_);
                    lean_dec(v___x_5097_);
                    v___x_5100_ = lean_box(0);
                    v_isShared_5101_ = v_isSharedCheck_5105_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_5101_ == 0 {
                    v___x_5103_ = v___x_5100_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5104_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_a_5098_);
                    v___x_5103_ = v_reuseFailAlloc_5104_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5103_;
            }
            15 => {
                if v_isShared_5112_ == 0 {
                    v___x_5114_ = v___x_5111_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5109_);
                    v___x_5114_ = v_reuseFailAlloc_5115_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5114_;
            }
            17 => {
                if v_isShared_5120_ == 0 {
                    v___x_5122_ = v___x_5119_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5123_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5123_, 0, v_a_5117_);
                    v___x_5122_ = v_reuseFailAlloc_5123_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___boxed(
    mut v_stx_5125_: *mut LeanObject,
    mut v_a_5126_: *mut LeanObject,
    mut v_a_5127_: *mut LeanObject,
    mut v_a_5128_: *mut LeanObject,
    mut v_a_5129_: *mut LeanObject,
    mut v_a_5130_: *mut LeanObject,
    mut v_a_5131_: *mut LeanObject,
    mut v_a_5132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5133_: *mut LeanObject = core::ptr::null_mut();
    v_res_5133_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(v_stx_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_);
    lean_dec(v_a_5131_);
    lean_dec_ref(v_a_5130_);
    lean_dec(v_a_5129_);
    lean_dec_ref(v_a_5128_);
    lean_dec(v_a_5127_);
    lean_dec_ref(v_a_5126_);
    return v_res_5133_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0(
    mut v_config_5203_: *mut LeanObject,
    mut v_item_5204_: *mut LeanObject,
    mut v___y_5205_: *mut LeanObject,
    mut v___y_5206_: *mut LeanObject,
    mut v___y_5207_: *mut LeanObject,
    mut v___y_5208_: *mut LeanObject,
    mut v___y_5209_: *mut LeanObject,
    mut v___y_5210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_item_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: u8 = 0;
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: u8 = 0;
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: u8 = 0;
    let mut v___x_5231_: u8 = 0;
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: u8 = 0;
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: u8 = 0;
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: u8 = 0;
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5243_: u8 = 0;
    let mut v_proofs_5244_: u8 = 0;
    let mut v_types_5245_: u8 = 0;
    let mut v_implicits_5246_: u8 = 0;
    let mut v_descend_5247_: u8 = 0;
    let mut v_underBinder_5248_: u8 = 0;
    let mut v_merge_5249_: u8 = 0;
    let mut v_useContext_5250_: u8 = 0;
    let mut v_onlyGivenNames_5251_: u8 = 0;
    let mut v_preserveBinderNames_5252_: u8 = 0;
    let mut v_lift_5253_: u8 = 0;
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5256_: u8 = 0;
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: u8 = 0;
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5264_: u8 = 0;
    let mut v_isSharedCheck_5265_: u8 = 0;
    let mut v_a_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5273_: u8 = 0;
    let mut v_a_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5277_: u8 = 0;
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5281_: u8 = 0;
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: u8 = 0;
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5289_: u8 = 0;
    let mut v_proofs_5290_: u8 = 0;
    let mut v_types_5291_: u8 = 0;
    let mut v_implicits_5292_: u8 = 0;
    let mut v_descend_5293_: u8 = 0;
    let mut v_underBinder_5294_: u8 = 0;
    let mut v_usedOnly_5295_: u8 = 0;
    let mut v_merge_5296_: u8 = 0;
    let mut v_onlyGivenNames_5297_: u8 = 0;
    let mut v_preserveBinderNames_5298_: u8 = 0;
    let mut v_lift_5299_: u8 = 0;
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5302_: u8 = 0;
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: u8 = 0;
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5310_: u8 = 0;
    let mut v_isSharedCheck_5311_: u8 = 0;
    let mut v_a_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5315_: u8 = 0;
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5319_: u8 = 0;
    let mut v_a_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5323_: u8 = 0;
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5327_: u8 = 0;
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: u8 = 0;
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5335_: u8 = 0;
    let mut v_proofs_5336_: u8 = 0;
    let mut v_types_5337_: u8 = 0;
    let mut v_implicits_5338_: u8 = 0;
    let mut v_descend_5339_: u8 = 0;
    let mut v_usedOnly_5340_: u8 = 0;
    let mut v_merge_5341_: u8 = 0;
    let mut v_useContext_5342_: u8 = 0;
    let mut v_onlyGivenNames_5343_: u8 = 0;
    let mut v_preserveBinderNames_5344_: u8 = 0;
    let mut v_lift_5345_: u8 = 0;
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5348_: u8 = 0;
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: u8 = 0;
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5356_: u8 = 0;
    let mut v_isSharedCheck_5357_: u8 = 0;
    let mut v_a_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5361_: u8 = 0;
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5365_: u8 = 0;
    let mut v_a_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5369_: u8 = 0;
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5373_: u8 = 0;
    let mut v___x_5374_: u8 = 0;
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: u8 = 0;
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: u8 = 0;
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: u8 = 0;
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5386_: u8 = 0;
    let mut v_proofs_5387_: u8 = 0;
    let mut v_implicits_5388_: u8 = 0;
    let mut v_descend_5389_: u8 = 0;
    let mut v_underBinder_5390_: u8 = 0;
    let mut v_usedOnly_5391_: u8 = 0;
    let mut v_merge_5392_: u8 = 0;
    let mut v_useContext_5393_: u8 = 0;
    let mut v_onlyGivenNames_5394_: u8 = 0;
    let mut v_preserveBinderNames_5395_: u8 = 0;
    let mut v_lift_5396_: u8 = 0;
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5399_: u8 = 0;
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: u8 = 0;
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5407_: u8 = 0;
    let mut v_isSharedCheck_5408_: u8 = 0;
    let mut v_a_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5412_: u8 = 0;
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5416_: u8 = 0;
    let mut v_a_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5420_: u8 = 0;
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5424_: u8 = 0;
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: u8 = 0;
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5432_: u8 = 0;
    let mut v_types_5433_: u8 = 0;
    let mut v_implicits_5434_: u8 = 0;
    let mut v_descend_5435_: u8 = 0;
    let mut v_underBinder_5436_: u8 = 0;
    let mut v_usedOnly_5437_: u8 = 0;
    let mut v_merge_5438_: u8 = 0;
    let mut v_useContext_5439_: u8 = 0;
    let mut v_onlyGivenNames_5440_: u8 = 0;
    let mut v_preserveBinderNames_5441_: u8 = 0;
    let mut v_lift_5442_: u8 = 0;
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5445_: u8 = 0;
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: u8 = 0;
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5453_: u8 = 0;
    let mut v_isSharedCheck_5454_: u8 = 0;
    let mut v_a_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5458_: u8 = 0;
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5462_: u8 = 0;
    let mut v_a_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5466_: u8 = 0;
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5470_: u8 = 0;
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: u8 = 0;
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5478_: u8 = 0;
    let mut v_proofs_5479_: u8 = 0;
    let mut v_types_5480_: u8 = 0;
    let mut v_implicits_5481_: u8 = 0;
    let mut v_descend_5482_: u8 = 0;
    let mut v_underBinder_5483_: u8 = 0;
    let mut v_usedOnly_5484_: u8 = 0;
    let mut v_merge_5485_: u8 = 0;
    let mut v_useContext_5486_: u8 = 0;
    let mut v_onlyGivenNames_5487_: u8 = 0;
    let mut v_lift_5488_: u8 = 0;
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5491_: u8 = 0;
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: u8 = 0;
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5499_: u8 = 0;
    let mut v_isSharedCheck_5500_: u8 = 0;
    let mut v_a_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5504_: u8 = 0;
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5508_: u8 = 0;
    let mut v_a_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5512_: u8 = 0;
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5516_: u8 = 0;
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: u8 = 0;
    let mut v___x_5519_: u8 = 0;
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: u8 = 0;
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: u8 = 0;
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: u8 = 0;
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5531_: u8 = 0;
    let mut v_proofs_5532_: u8 = 0;
    let mut v_types_5533_: u8 = 0;
    let mut v_implicits_5534_: u8 = 0;
    let mut v_descend_5535_: u8 = 0;
    let mut v_underBinder_5536_: u8 = 0;
    let mut v_usedOnly_5537_: u8 = 0;
    let mut v_merge_5538_: u8 = 0;
    let mut v_useContext_5539_: u8 = 0;
    let mut v_preserveBinderNames_5540_: u8 = 0;
    let mut v_lift_5541_: u8 = 0;
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5544_: u8 = 0;
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: u8 = 0;
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5552_: u8 = 0;
    let mut v_isSharedCheck_5553_: u8 = 0;
    let mut v_a_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5557_: u8 = 0;
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5561_: u8 = 0;
    let mut v_a_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5565_: u8 = 0;
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5569_: u8 = 0;
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: u8 = 0;
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5577_: u8 = 0;
    let mut v_proofs_5578_: u8 = 0;
    let mut v_types_5579_: u8 = 0;
    let mut v_implicits_5580_: u8 = 0;
    let mut v_descend_5581_: u8 = 0;
    let mut v_underBinder_5582_: u8 = 0;
    let mut v_usedOnly_5583_: u8 = 0;
    let mut v_useContext_5584_: u8 = 0;
    let mut v_onlyGivenNames_5585_: u8 = 0;
    let mut v_preserveBinderNames_5586_: u8 = 0;
    let mut v_lift_5587_: u8 = 0;
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5590_: u8 = 0;
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: u8 = 0;
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5598_: u8 = 0;
    let mut v_isSharedCheck_5599_: u8 = 0;
    let mut v_a_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5603_: u8 = 0;
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5607_: u8 = 0;
    let mut v_a_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5611_: u8 = 0;
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5615_: u8 = 0;
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: u8 = 0;
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5623_: u8 = 0;
    let mut v_proofs_5624_: u8 = 0;
    let mut v_types_5625_: u8 = 0;
    let mut v_implicits_5626_: u8 = 0;
    let mut v_descend_5627_: u8 = 0;
    let mut v_underBinder_5628_: u8 = 0;
    let mut v_usedOnly_5629_: u8 = 0;
    let mut v_merge_5630_: u8 = 0;
    let mut v_useContext_5631_: u8 = 0;
    let mut v_onlyGivenNames_5632_: u8 = 0;
    let mut v_preserveBinderNames_5633_: u8 = 0;
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5636_: u8 = 0;
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: u8 = 0;
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5644_: u8 = 0;
    let mut v_isSharedCheck_5645_: u8 = 0;
    let mut v_a_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5649_: u8 = 0;
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5653_: u8 = 0;
    let mut v_a_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5657_: u8 = 0;
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5661_: u8 = 0;
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: u8 = 0;
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: u8 = 0;
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: u8 = 0;
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: u8 = 0;
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5675_: u8 = 0;
    let mut v_proofs_5676_: u8 = 0;
    let mut v_types_5677_: u8 = 0;
    let mut v_descend_5678_: u8 = 0;
    let mut v_underBinder_5679_: u8 = 0;
    let mut v_usedOnly_5680_: u8 = 0;
    let mut v_merge_5681_: u8 = 0;
    let mut v_useContext_5682_: u8 = 0;
    let mut v_onlyGivenNames_5683_: u8 = 0;
    let mut v_preserveBinderNames_5684_: u8 = 0;
    let mut v_lift_5685_: u8 = 0;
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5688_: u8 = 0;
    let mut v___x_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: u8 = 0;
    let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5696_: u8 = 0;
    let mut v_isSharedCheck_5697_: u8 = 0;
    let mut v_a_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5701_: u8 = 0;
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5705_: u8 = 0;
    let mut v_a_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5709_: u8 = 0;
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5713_: u8 = 0;
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: u8 = 0;
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5721_: u8 = 0;
    let mut v_proofs_5722_: u8 = 0;
    let mut v_types_5723_: u8 = 0;
    let mut v_implicits_5724_: u8 = 0;
    let mut v_underBinder_5725_: u8 = 0;
    let mut v_usedOnly_5726_: u8 = 0;
    let mut v_merge_5727_: u8 = 0;
    let mut v_useContext_5728_: u8 = 0;
    let mut v_onlyGivenNames_5729_: u8 = 0;
    let mut v_preserveBinderNames_5730_: u8 = 0;
    let mut v_lift_5731_: u8 = 0;
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5734_: u8 = 0;
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: u8 = 0;
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5742_: u8 = 0;
    let mut v_isSharedCheck_5743_: u8 = 0;
    let mut v_a_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5747_: u8 = 0;
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5751_: u8 = 0;
    let mut v_a_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5755_: u8 = 0;
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5759_: u8 = 0;
    let mut v___x_5760_: u8 = 0;
    let mut v_value_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5766_: u8 = 0;
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5222_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3;
                v___x_5223_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(
                    v_item_5204_,
                    v___x_5222_,
                    v___y_5205_,
                    v___y_5206_,
                    v___y_5207_,
                    v___y_5208_,
                    v___y_5209_,
                    v___y_5210_,
                );
                if lean_obj_tag(v___x_5223_) == 0 {
                    lean_dec_ref_known(v___x_5223_, 1);
                    v___x_5224_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_5204_);
                    if v___x_5224_ == 0 {
                        v___x_5225_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_5204_);
                        lean_inc_ref(v_item_5204_);
                        v___x_5226_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_5204_);
                        v___x_5227_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1;
                        v___x_5228_ = lean_string_dec_lt(v___x_5225_, v___x_5227_);
                        if v___x_5228_ == 0 {
                            v___x_5229_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2;
                            v___x_5230_ = lean_string_dec_lt(v___x_5225_, v___x_5229_);
                            if v___x_5230_ == 0 {
                                v___x_5231_ = lean_string_dec_eq(v___x_5225_, v___x_5229_);
                                if v___x_5231_ == 0 {
                                    v___x_5232_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3;
                                    v___x_5233_ = lean_string_dec_eq(v___x_5225_, v___x_5232_);
                                    if v___x_5233_ == 0 {
                                        v___x_5234_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4;
                                        v___x_5235_ = lean_string_dec_eq(v___x_5225_, v___x_5234_);
                                        lean_dec_ref(v___x_5225_);
                                        if v___x_5235_ == 0 {
                                            lean_dec_ref(v_item_5204_);
                                            lean_dec_ref(v_config_5203_);
                                            v_item_5213_ = v___x_5226_;
                                            v___y_5214_ = v___y_5205_;
                                            v___y_5215_ = v___y_5206_;
                                            v___y_5216_ = v___y_5207_;
                                            v___y_5217_ = v___y_5208_;
                                            v___y_5218_ = v___y_5209_;
                                            v___y_5219_ = v___y_5210_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_5236_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5;
                                            v___x_5237_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                    v_item_5204_,
                                                    v___x_5236_,
                                                    v___y_5205_,
                                                    v___y_5206_,
                                                    v___y_5207_,
                                                    v___y_5208_,
                                                    v___y_5209_,
                                                    v___y_5210_,
                                                );
                                            if lean_obj_tag(v___x_5237_) == 0 {
                                                lean_dec_ref_known(v___x_5237_, 1);
                                                v___x_5238_ =
                                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                        v___x_5226_,
                                                    );
                                                if v___x_5238_ == 0 {
                                                    lean_dec_ref(v_item_5204_);
                                                    lean_dec_ref(v_config_5203_);
                                                    v_item_5213_ = v___x_5226_;
                                                    v___y_5214_ = v___y_5205_;
                                                    v___y_5215_ = v___y_5206_;
                                                    v___y_5216_ = v___y_5207_;
                                                    v___y_5217_ = v___y_5208_;
                                                    v___y_5218_ = v___y_5209_;
                                                    v___y_5219_ = v___y_5210_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec_ref(v___x_5226_);
                                                    v___x_5239_ =
                                                        l_Lean_Elab_ConfigEval_evalBoolItem(
                                                            v_item_5204_,
                                                            v___y_5205_,
                                                            v___y_5206_,
                                                            v___y_5207_,
                                                            v___y_5208_,
                                                            v___y_5209_,
                                                            v___y_5210_,
                                                        );
                                                    if lean_obj_tag(v___x_5239_) == 0 {
                                                        v_a_5240_ = lean_ctor_get(v___x_5239_, 0);
                                                        v_isSharedCheck_5265_ =
                                                            (!lean_is_exclusive(v___x_5239_)) as u8;
                                                        if v_isSharedCheck_5265_ == 0 {
                                                            v___x_5242_ = v___x_5239_;
                                                            v_isShared_5243_ =
                                                                v_isSharedCheck_5265_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_5240_);
                                                            lean_dec(v___x_5239_);
                                                            v___x_5242_ = lean_box(0);
                                                            v_isShared_5243_ =
                                                                v_isSharedCheck_5265_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_config_5203_);
                                                        v_a_5266_ = lean_ctor_get(v___x_5239_, 0);
                                                        v_isSharedCheck_5273_ =
                                                            (!lean_is_exclusive(v___x_5239_)) as u8;
                                                        if v_isSharedCheck_5273_ == 0 {
                                                            v___x_5268_ = v___x_5239_;
                                                            v_isShared_5269_ =
                                                                v_isSharedCheck_5273_;
                                                            state = 6;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_5266_);
                                                            lean_dec(v___x_5239_);
                                                            v___x_5268_ = lean_box(0);
                                                            v_isShared_5269_ =
                                                                v_isSharedCheck_5273_;
                                                            state = 6;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_5226_);
                                                lean_dec_ref(v_item_5204_);
                                                lean_dec_ref(v_config_5203_);
                                                v_a_5274_ = lean_ctor_get(v___x_5237_, 0);
                                                v_isSharedCheck_5281_ =
                                                    (!lean_is_exclusive(v___x_5237_)) as u8;
                                                if v_isSharedCheck_5281_ == 0 {
                                                    v___x_5276_ = v___x_5237_;
                                                    v_isShared_5277_ = v_isSharedCheck_5281_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5274_);
                                                    lean_dec(v___x_5237_);
                                                    v___x_5276_ = lean_box(0);
                                                    v_isShared_5277_ = v_isSharedCheck_5281_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_5225_);
                                        v___x_5282_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6;
                                        v___x_5283_ =
                                            l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                v_item_5204_,
                                                v___x_5282_,
                                                v___y_5205_,
                                                v___y_5206_,
                                                v___y_5207_,
                                                v___y_5208_,
                                                v___y_5209_,
                                                v___y_5210_,
                                            );
                                        if lean_obj_tag(v___x_5283_) == 0 {
                                            lean_dec_ref_known(v___x_5283_, 1);
                                            v___x_5284_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                    v___x_5226_,
                                                );
                                            if v___x_5284_ == 0 {
                                                lean_dec_ref(v_item_5204_);
                                                lean_dec_ref(v_config_5203_);
                                                v_item_5213_ = v___x_5226_;
                                                v___y_5214_ = v___y_5205_;
                                                v___y_5215_ = v___y_5206_;
                                                v___y_5216_ = v___y_5207_;
                                                v___y_5217_ = v___y_5208_;
                                                v___y_5218_ = v___y_5209_;
                                                v___y_5219_ = v___y_5210_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec_ref(v___x_5226_);
                                                v___x_5285_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                    v_item_5204_,
                                                    v___y_5205_,
                                                    v___y_5206_,
                                                    v___y_5207_,
                                                    v___y_5208_,
                                                    v___y_5209_,
                                                    v___y_5210_,
                                                );
                                                if lean_obj_tag(v___x_5285_) == 0 {
                                                    v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
                                                    v_isSharedCheck_5311_ =
                                                        (!lean_is_exclusive(v___x_5285_)) as u8;
                                                    if v_isSharedCheck_5311_ == 0 {
                                                        v___x_5288_ = v___x_5285_;
                                                        v_isShared_5289_ = v_isSharedCheck_5311_;
                                                        state = 10;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5286_);
                                                        lean_dec(v___x_5285_);
                                                        v___x_5288_ = lean_box(0);
                                                        v_isShared_5289_ = v_isSharedCheck_5311_;
                                                        state = 10;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_config_5203_);
                                                    v_a_5312_ = lean_ctor_get(v___x_5285_, 0);
                                                    v_isSharedCheck_5319_ =
                                                        (!lean_is_exclusive(v___x_5285_)) as u8;
                                                    if v_isSharedCheck_5319_ == 0 {
                                                        v___x_5314_ = v___x_5285_;
                                                        v_isShared_5315_ = v_isSharedCheck_5319_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5312_);
                                                        lean_dec(v___x_5285_);
                                                        v___x_5314_ = lean_box(0);
                                                        v_isShared_5315_ = v_isSharedCheck_5319_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_5226_);
                                            lean_dec_ref(v_item_5204_);
                                            lean_dec_ref(v_config_5203_);
                                            v_a_5320_ = lean_ctor_get(v___x_5283_, 0);
                                            v_isSharedCheck_5327_ =
                                                (!lean_is_exclusive(v___x_5283_)) as u8;
                                            if v_isSharedCheck_5327_ == 0 {
                                                v___x_5322_ = v___x_5283_;
                                                v_isShared_5323_ = v_isSharedCheck_5327_;
                                                state = 16;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5320_);
                                                lean_dec(v___x_5283_);
                                                v___x_5322_ = lean_box(0);
                                                v_isShared_5323_ = v_isSharedCheck_5327_;
                                                state = 16;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_5225_);
                                    v___x_5328_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7;
                                    v___x_5329_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                        v_item_5204_,
                                        v___x_5328_,
                                        v___y_5205_,
                                        v___y_5206_,
                                        v___y_5207_,
                                        v___y_5208_,
                                        v___y_5209_,
                                        v___y_5210_,
                                    );
                                    if lean_obj_tag(v___x_5329_) == 0 {
                                        lean_dec_ref_known(v___x_5329_, 1);
                                        v___x_5330_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                            v___x_5226_,
                                        );
                                        if v___x_5330_ == 0 {
                                            lean_dec_ref(v_item_5204_);
                                            lean_dec_ref(v_config_5203_);
                                            v_item_5213_ = v___x_5226_;
                                            v___y_5214_ = v___y_5205_;
                                            v___y_5215_ = v___y_5206_;
                                            v___y_5216_ = v___y_5207_;
                                            v___y_5217_ = v___y_5208_;
                                            v___y_5218_ = v___y_5209_;
                                            v___y_5219_ = v___y_5210_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec_ref(v___x_5226_);
                                            v___x_5331_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                v_item_5204_,
                                                v___y_5205_,
                                                v___y_5206_,
                                                v___y_5207_,
                                                v___y_5208_,
                                                v___y_5209_,
                                                v___y_5210_,
                                            );
                                            if lean_obj_tag(v___x_5331_) == 0 {
                                                v_a_5332_ = lean_ctor_get(v___x_5331_, 0);
                                                v_isSharedCheck_5357_ =
                                                    (!lean_is_exclusive(v___x_5331_)) as u8;
                                                if v_isSharedCheck_5357_ == 0 {
                                                    v___x_5334_ = v___x_5331_;
                                                    v_isShared_5335_ = v_isSharedCheck_5357_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5332_);
                                                    lean_dec(v___x_5331_);
                                                    v___x_5334_ = lean_box(0);
                                                    v_isShared_5335_ = v_isSharedCheck_5357_;
                                                    state = 18;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_config_5203_);
                                                v_a_5358_ = lean_ctor_get(v___x_5331_, 0);
                                                v_isSharedCheck_5365_ =
                                                    (!lean_is_exclusive(v___x_5331_)) as u8;
                                                if v_isSharedCheck_5365_ == 0 {
                                                    v___x_5360_ = v___x_5331_;
                                                    v_isShared_5361_ = v_isSharedCheck_5365_;
                                                    state = 22;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5358_);
                                                    lean_dec(v___x_5331_);
                                                    v___x_5360_ = lean_box(0);
                                                    v_isShared_5361_ = v_isSharedCheck_5365_;
                                                    state = 22;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_5226_);
                                        lean_dec_ref(v_item_5204_);
                                        lean_dec_ref(v_config_5203_);
                                        v_a_5366_ = lean_ctor_get(v___x_5329_, 0);
                                        v_isSharedCheck_5373_ =
                                            (!lean_is_exclusive(v___x_5329_)) as u8;
                                        if v_isSharedCheck_5373_ == 0 {
                                            v___x_5368_ = v___x_5329_;
                                            v_isShared_5369_ = v_isSharedCheck_5373_;
                                            state = 24;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5366_);
                                            lean_dec(v___x_5329_);
                                            v___x_5368_ = lean_box(0);
                                            v_isShared_5369_ = v_isSharedCheck_5373_;
                                            state = 24;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_5374_ = lean_string_dec_eq(v___x_5225_, v___x_5227_);
                                if v___x_5374_ == 0 {
                                    v___x_5375_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8;
                                    v___x_5376_ = lean_string_dec_eq(v___x_5225_, v___x_5375_);
                                    if v___x_5376_ == 0 {
                                        v___x_5377_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9;
                                        v___x_5378_ = lean_string_dec_eq(v___x_5225_, v___x_5377_);
                                        lean_dec_ref(v___x_5225_);
                                        if v___x_5378_ == 0 {
                                            lean_dec_ref(v_item_5204_);
                                            lean_dec_ref(v_config_5203_);
                                            v_item_5213_ = v___x_5226_;
                                            v___y_5214_ = v___y_5205_;
                                            v___y_5215_ = v___y_5206_;
                                            v___y_5216_ = v___y_5207_;
                                            v___y_5217_ = v___y_5208_;
                                            v___y_5218_ = v___y_5209_;
                                            v___y_5219_ = v___y_5210_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_5379_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10;
                                            v___x_5380_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                    v_item_5204_,
                                                    v___x_5379_,
                                                    v___y_5205_,
                                                    v___y_5206_,
                                                    v___y_5207_,
                                                    v___y_5208_,
                                                    v___y_5209_,
                                                    v___y_5210_,
                                                );
                                            if lean_obj_tag(v___x_5380_) == 0 {
                                                lean_dec_ref_known(v___x_5380_, 1);
                                                v___x_5381_ =
                                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                        v___x_5226_,
                                                    );
                                                if v___x_5381_ == 0 {
                                                    lean_dec_ref(v_item_5204_);
                                                    lean_dec_ref(v_config_5203_);
                                                    v_item_5213_ = v___x_5226_;
                                                    v___y_5214_ = v___y_5205_;
                                                    v___y_5215_ = v___y_5206_;
                                                    v___y_5216_ = v___y_5207_;
                                                    v___y_5217_ = v___y_5208_;
                                                    v___y_5218_ = v___y_5209_;
                                                    v___y_5219_ = v___y_5210_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec_ref(v___x_5226_);
                                                    v___x_5382_ =
                                                        l_Lean_Elab_ConfigEval_evalBoolItem(
                                                            v_item_5204_,
                                                            v___y_5205_,
                                                            v___y_5206_,
                                                            v___y_5207_,
                                                            v___y_5208_,
                                                            v___y_5209_,
                                                            v___y_5210_,
                                                        );
                                                    if lean_obj_tag(v___x_5382_) == 0 {
                                                        v_a_5383_ = lean_ctor_get(v___x_5382_, 0);
                                                        v_isSharedCheck_5408_ =
                                                            (!lean_is_exclusive(v___x_5382_)) as u8;
                                                        if v_isSharedCheck_5408_ == 0 {
                                                            v___x_5385_ = v___x_5382_;
                                                            v_isShared_5386_ =
                                                                v_isSharedCheck_5408_;
                                                            state = 26;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_5383_);
                                                            lean_dec(v___x_5382_);
                                                            v___x_5385_ = lean_box(0);
                                                            v_isShared_5386_ =
                                                                v_isSharedCheck_5408_;
                                                            state = 26;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_config_5203_);
                                                        v_a_5409_ = lean_ctor_get(v___x_5382_, 0);
                                                        v_isSharedCheck_5416_ =
                                                            (!lean_is_exclusive(v___x_5382_)) as u8;
                                                        if v_isSharedCheck_5416_ == 0 {
                                                            v___x_5411_ = v___x_5382_;
                                                            v_isShared_5412_ =
                                                                v_isSharedCheck_5416_;
                                                            state = 30;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_5409_);
                                                            lean_dec(v___x_5382_);
                                                            v___x_5411_ = lean_box(0);
                                                            v_isShared_5412_ =
                                                                v_isSharedCheck_5416_;
                                                            state = 30;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_5226_);
                                                lean_dec_ref(v_item_5204_);
                                                lean_dec_ref(v_config_5203_);
                                                v_a_5417_ = lean_ctor_get(v___x_5380_, 0);
                                                v_isSharedCheck_5424_ =
                                                    (!lean_is_exclusive(v___x_5380_)) as u8;
                                                if v_isSharedCheck_5424_ == 0 {
                                                    v___x_5419_ = v___x_5380_;
                                                    v_isShared_5420_ = v_isSharedCheck_5424_;
                                                    state = 32;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5417_);
                                                    lean_dec(v___x_5380_);
                                                    v___x_5419_ = lean_box(0);
                                                    v_isShared_5420_ = v_isSharedCheck_5424_;
                                                    state = 32;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_5225_);
                                        v___x_5425_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11;
                                        v___x_5426_ =
                                            l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                v_item_5204_,
                                                v___x_5425_,
                                                v___y_5205_,
                                                v___y_5206_,
                                                v___y_5207_,
                                                v___y_5208_,
                                                v___y_5209_,
                                                v___y_5210_,
                                            );
                                        if lean_obj_tag(v___x_5426_) == 0 {
                                            lean_dec_ref_known(v___x_5426_, 1);
                                            v___x_5427_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                    v___x_5226_,
                                                );
                                            if v___x_5427_ == 0 {
                                                lean_dec_ref(v_item_5204_);
                                                lean_dec_ref(v_config_5203_);
                                                v_item_5213_ = v___x_5226_;
                                                v___y_5214_ = v___y_5205_;
                                                v___y_5215_ = v___y_5206_;
                                                v___y_5216_ = v___y_5207_;
                                                v___y_5217_ = v___y_5208_;
                                                v___y_5218_ = v___y_5209_;
                                                v___y_5219_ = v___y_5210_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec_ref(v___x_5226_);
                                                v___x_5428_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                    v_item_5204_,
                                                    v___y_5205_,
                                                    v___y_5206_,
                                                    v___y_5207_,
                                                    v___y_5208_,
                                                    v___y_5209_,
                                                    v___y_5210_,
                                                );
                                                if lean_obj_tag(v___x_5428_) == 0 {
                                                    v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
                                                    v_isSharedCheck_5454_ =
                                                        (!lean_is_exclusive(v___x_5428_)) as u8;
                                                    if v_isSharedCheck_5454_ == 0 {
                                                        v___x_5431_ = v___x_5428_;
                                                        v_isShared_5432_ = v_isSharedCheck_5454_;
                                                        state = 34;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5429_);
                                                        lean_dec(v___x_5428_);
                                                        v___x_5431_ = lean_box(0);
                                                        v_isShared_5432_ = v_isSharedCheck_5454_;
                                                        state = 34;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_config_5203_);
                                                    v_a_5455_ = lean_ctor_get(v___x_5428_, 0);
                                                    v_isSharedCheck_5462_ =
                                                        (!lean_is_exclusive(v___x_5428_)) as u8;
                                                    if v_isSharedCheck_5462_ == 0 {
                                                        v___x_5457_ = v___x_5428_;
                                                        v_isShared_5458_ = v_isSharedCheck_5462_;
                                                        state = 38;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5455_);
                                                        lean_dec(v___x_5428_);
                                                        v___x_5457_ = lean_box(0);
                                                        v_isShared_5458_ = v_isSharedCheck_5462_;
                                                        state = 38;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_5226_);
                                            lean_dec_ref(v_item_5204_);
                                            lean_dec_ref(v_config_5203_);
                                            v_a_5463_ = lean_ctor_get(v___x_5426_, 0);
                                            v_isSharedCheck_5470_ =
                                                (!lean_is_exclusive(v___x_5426_)) as u8;
                                            if v_isSharedCheck_5470_ == 0 {
                                                v___x_5465_ = v___x_5426_;
                                                v_isShared_5466_ = v_isSharedCheck_5470_;
                                                state = 40;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5463_);
                                                lean_dec(v___x_5426_);
                                                v___x_5465_ = lean_box(0);
                                                v_isShared_5466_ = v_isSharedCheck_5470_;
                                                state = 40;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_5225_);
                                    v___x_5471_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12;
                                    v___x_5472_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                        v_item_5204_,
                                        v___x_5471_,
                                        v___y_5205_,
                                        v___y_5206_,
                                        v___y_5207_,
                                        v___y_5208_,
                                        v___y_5209_,
                                        v___y_5210_,
                                    );
                                    if lean_obj_tag(v___x_5472_) == 0 {
                                        lean_dec_ref_known(v___x_5472_, 1);
                                        v___x_5473_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                            v___x_5226_,
                                        );
                                        if v___x_5473_ == 0 {
                                            lean_dec_ref(v_item_5204_);
                                            lean_dec_ref(v_config_5203_);
                                            v_item_5213_ = v___x_5226_;
                                            v___y_5214_ = v___y_5205_;
                                            v___y_5215_ = v___y_5206_;
                                            v___y_5216_ = v___y_5207_;
                                            v___y_5217_ = v___y_5208_;
                                            v___y_5218_ = v___y_5209_;
                                            v___y_5219_ = v___y_5210_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec_ref(v___x_5226_);
                                            v___x_5474_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                v_item_5204_,
                                                v___y_5205_,
                                                v___y_5206_,
                                                v___y_5207_,
                                                v___y_5208_,
                                                v___y_5209_,
                                                v___y_5210_,
                                            );
                                            if lean_obj_tag(v___x_5474_) == 0 {
                                                v_a_5475_ = lean_ctor_get(v___x_5474_, 0);
                                                v_isSharedCheck_5500_ =
                                                    (!lean_is_exclusive(v___x_5474_)) as u8;
                                                if v_isSharedCheck_5500_ == 0 {
                                                    v___x_5477_ = v___x_5474_;
                                                    v_isShared_5478_ = v_isSharedCheck_5500_;
                                                    state = 42;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5475_);
                                                    lean_dec(v___x_5474_);
                                                    v___x_5477_ = lean_box(0);
                                                    v_isShared_5478_ = v_isSharedCheck_5500_;
                                                    state = 42;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_config_5203_);
                                                v_a_5501_ = lean_ctor_get(v___x_5474_, 0);
                                                v_isSharedCheck_5508_ =
                                                    (!lean_is_exclusive(v___x_5474_)) as u8;
                                                if v_isSharedCheck_5508_ == 0 {
                                                    v___x_5503_ = v___x_5474_;
                                                    v_isShared_5504_ = v_isSharedCheck_5508_;
                                                    state = 46;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5501_);
                                                    lean_dec(v___x_5474_);
                                                    v___x_5503_ = lean_box(0);
                                                    v_isShared_5504_ = v_isSharedCheck_5508_;
                                                    state = 46;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_5226_);
                                        lean_dec_ref(v_item_5204_);
                                        lean_dec_ref(v_config_5203_);
                                        v_a_5509_ = lean_ctor_get(v___x_5472_, 0);
                                        v_isSharedCheck_5516_ =
                                            (!lean_is_exclusive(v___x_5472_)) as u8;
                                        if v_isSharedCheck_5516_ == 0 {
                                            v___x_5511_ = v___x_5472_;
                                            v_isShared_5512_ = v_isSharedCheck_5516_;
                                            state = 48;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5509_);
                                            lean_dec(v___x_5472_);
                                            v___x_5511_ = lean_box(0);
                                            v_isShared_5512_ = v_isSharedCheck_5516_;
                                            state = 48;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_5517_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13;
                            v___x_5518_ = lean_string_dec_lt(v___x_5225_, v___x_5517_);
                            if v___x_5518_ == 0 {
                                v___x_5519_ = lean_string_dec_eq(v___x_5225_, v___x_5517_);
                                if v___x_5519_ == 0 {
                                    v___x_5520_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14;
                                    v___x_5521_ = lean_string_dec_eq(v___x_5225_, v___x_5520_);
                                    if v___x_5521_ == 0 {
                                        v___x_5522_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15;
                                        v___x_5523_ = lean_string_dec_eq(v___x_5225_, v___x_5522_);
                                        lean_dec_ref(v___x_5225_);
                                        if v___x_5523_ == 0 {
                                            lean_dec_ref(v_item_5204_);
                                            lean_dec_ref(v_config_5203_);
                                            v_item_5213_ = v___x_5226_;
                                            v___y_5214_ = v___y_5205_;
                                            v___y_5215_ = v___y_5206_;
                                            v___y_5216_ = v___y_5207_;
                                            v___y_5217_ = v___y_5208_;
                                            v___y_5218_ = v___y_5209_;
                                            v___y_5219_ = v___y_5210_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_5524_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16;
                                            v___x_5525_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                    v_item_5204_,
                                                    v___x_5524_,
                                                    v___y_5205_,
                                                    v___y_5206_,
                                                    v___y_5207_,
                                                    v___y_5208_,
                                                    v___y_5209_,
                                                    v___y_5210_,
                                                );
                                            if lean_obj_tag(v___x_5525_) == 0 {
                                                lean_dec_ref_known(v___x_5525_, 1);
                                                v___x_5526_ =
                                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                        v___x_5226_,
                                                    );
                                                if v___x_5526_ == 0 {
                                                    lean_dec_ref(v_item_5204_);
                                                    lean_dec_ref(v_config_5203_);
                                                    v_item_5213_ = v___x_5226_;
                                                    v___y_5214_ = v___y_5205_;
                                                    v___y_5215_ = v___y_5206_;
                                                    v___y_5216_ = v___y_5207_;
                                                    v___y_5217_ = v___y_5208_;
                                                    v___y_5218_ = v___y_5209_;
                                                    v___y_5219_ = v___y_5210_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec_ref(v___x_5226_);
                                                    v___x_5527_ =
                                                        l_Lean_Elab_ConfigEval_evalBoolItem(
                                                            v_item_5204_,
                                                            v___y_5205_,
                                                            v___y_5206_,
                                                            v___y_5207_,
                                                            v___y_5208_,
                                                            v___y_5209_,
                                                            v___y_5210_,
                                                        );
                                                    if lean_obj_tag(v___x_5527_) == 0 {
                                                        v_a_5528_ = lean_ctor_get(v___x_5527_, 0);
                                                        v_isSharedCheck_5553_ =
                                                            (!lean_is_exclusive(v___x_5527_)) as u8;
                                                        if v_isSharedCheck_5553_ == 0 {
                                                            v___x_5530_ = v___x_5527_;
                                                            v_isShared_5531_ =
                                                                v_isSharedCheck_5553_;
                                                            state = 50;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_5528_);
                                                            lean_dec(v___x_5527_);
                                                            v___x_5530_ = lean_box(0);
                                                            v_isShared_5531_ =
                                                                v_isSharedCheck_5553_;
                                                            state = 50;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_config_5203_);
                                                        v_a_5554_ = lean_ctor_get(v___x_5527_, 0);
                                                        v_isSharedCheck_5561_ =
                                                            (!lean_is_exclusive(v___x_5527_)) as u8;
                                                        if v_isSharedCheck_5561_ == 0 {
                                                            v___x_5556_ = v___x_5527_;
                                                            v_isShared_5557_ =
                                                                v_isSharedCheck_5561_;
                                                            state = 54;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_5554_);
                                                            lean_dec(v___x_5527_);
                                                            v___x_5556_ = lean_box(0);
                                                            v_isShared_5557_ =
                                                                v_isSharedCheck_5561_;
                                                            state = 54;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_5226_);
                                                lean_dec_ref(v_item_5204_);
                                                lean_dec_ref(v_config_5203_);
                                                v_a_5562_ = lean_ctor_get(v___x_5525_, 0);
                                                v_isSharedCheck_5569_ =
                                                    (!lean_is_exclusive(v___x_5525_)) as u8;
                                                if v_isSharedCheck_5569_ == 0 {
                                                    v___x_5564_ = v___x_5525_;
                                                    v_isShared_5565_ = v_isSharedCheck_5569_;
                                                    state = 56;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5562_);
                                                    lean_dec(v___x_5525_);
                                                    v___x_5564_ = lean_box(0);
                                                    v_isShared_5565_ = v_isSharedCheck_5569_;
                                                    state = 56;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_5225_);
                                        v___x_5570_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17;
                                        v___x_5571_ =
                                            l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                v_item_5204_,
                                                v___x_5570_,
                                                v___y_5205_,
                                                v___y_5206_,
                                                v___y_5207_,
                                                v___y_5208_,
                                                v___y_5209_,
                                                v___y_5210_,
                                            );
                                        if lean_obj_tag(v___x_5571_) == 0 {
                                            lean_dec_ref_known(v___x_5571_, 1);
                                            v___x_5572_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                    v___x_5226_,
                                                );
                                            if v___x_5572_ == 0 {
                                                lean_dec_ref(v_item_5204_);
                                                lean_dec_ref(v_config_5203_);
                                                v_item_5213_ = v___x_5226_;
                                                v___y_5214_ = v___y_5205_;
                                                v___y_5215_ = v___y_5206_;
                                                v___y_5216_ = v___y_5207_;
                                                v___y_5217_ = v___y_5208_;
                                                v___y_5218_ = v___y_5209_;
                                                v___y_5219_ = v___y_5210_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec_ref(v___x_5226_);
                                                v___x_5573_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                    v_item_5204_,
                                                    v___y_5205_,
                                                    v___y_5206_,
                                                    v___y_5207_,
                                                    v___y_5208_,
                                                    v___y_5209_,
                                                    v___y_5210_,
                                                );
                                                if lean_obj_tag(v___x_5573_) == 0 {
                                                    v_a_5574_ = lean_ctor_get(v___x_5573_, 0);
                                                    v_isSharedCheck_5599_ =
                                                        (!lean_is_exclusive(v___x_5573_)) as u8;
                                                    if v_isSharedCheck_5599_ == 0 {
                                                        v___x_5576_ = v___x_5573_;
                                                        v_isShared_5577_ = v_isSharedCheck_5599_;
                                                        state = 58;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5574_);
                                                        lean_dec(v___x_5573_);
                                                        v___x_5576_ = lean_box(0);
                                                        v_isShared_5577_ = v_isSharedCheck_5599_;
                                                        state = 58;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_config_5203_);
                                                    v_a_5600_ = lean_ctor_get(v___x_5573_, 0);
                                                    v_isSharedCheck_5607_ =
                                                        (!lean_is_exclusive(v___x_5573_)) as u8;
                                                    if v_isSharedCheck_5607_ == 0 {
                                                        v___x_5602_ = v___x_5573_;
                                                        v_isShared_5603_ = v_isSharedCheck_5607_;
                                                        state = 62;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5600_);
                                                        lean_dec(v___x_5573_);
                                                        v___x_5602_ = lean_box(0);
                                                        v_isShared_5603_ = v_isSharedCheck_5607_;
                                                        state = 62;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_5226_);
                                            lean_dec_ref(v_item_5204_);
                                            lean_dec_ref(v_config_5203_);
                                            v_a_5608_ = lean_ctor_get(v___x_5571_, 0);
                                            v_isSharedCheck_5615_ =
                                                (!lean_is_exclusive(v___x_5571_)) as u8;
                                            if v_isSharedCheck_5615_ == 0 {
                                                v___x_5610_ = v___x_5571_;
                                                v_isShared_5611_ = v_isSharedCheck_5615_;
                                                state = 64;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5608_);
                                                lean_dec(v___x_5571_);
                                                v___x_5610_ = lean_box(0);
                                                v_isShared_5611_ = v_isSharedCheck_5615_;
                                                state = 64;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_5225_);
                                    v___x_5616_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18;
                                    v___x_5617_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                        v_item_5204_,
                                        v___x_5616_,
                                        v___y_5205_,
                                        v___y_5206_,
                                        v___y_5207_,
                                        v___y_5208_,
                                        v___y_5209_,
                                        v___y_5210_,
                                    );
                                    if lean_obj_tag(v___x_5617_) == 0 {
                                        lean_dec_ref_known(v___x_5617_, 1);
                                        v___x_5618_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                            v___x_5226_,
                                        );
                                        if v___x_5618_ == 0 {
                                            lean_dec_ref(v_item_5204_);
                                            lean_dec_ref(v_config_5203_);
                                            v_item_5213_ = v___x_5226_;
                                            v___y_5214_ = v___y_5205_;
                                            v___y_5215_ = v___y_5206_;
                                            v___y_5216_ = v___y_5207_;
                                            v___y_5217_ = v___y_5208_;
                                            v___y_5218_ = v___y_5209_;
                                            v___y_5219_ = v___y_5210_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec_ref(v___x_5226_);
                                            v___x_5619_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                v_item_5204_,
                                                v___y_5205_,
                                                v___y_5206_,
                                                v___y_5207_,
                                                v___y_5208_,
                                                v___y_5209_,
                                                v___y_5210_,
                                            );
                                            if lean_obj_tag(v___x_5619_) == 0 {
                                                v_a_5620_ = lean_ctor_get(v___x_5619_, 0);
                                                v_isSharedCheck_5645_ =
                                                    (!lean_is_exclusive(v___x_5619_)) as u8;
                                                if v_isSharedCheck_5645_ == 0 {
                                                    v___x_5622_ = v___x_5619_;
                                                    v_isShared_5623_ = v_isSharedCheck_5645_;
                                                    state = 66;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5620_);
                                                    lean_dec(v___x_5619_);
                                                    v___x_5622_ = lean_box(0);
                                                    v_isShared_5623_ = v_isSharedCheck_5645_;
                                                    state = 66;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_config_5203_);
                                                v_a_5646_ = lean_ctor_get(v___x_5619_, 0);
                                                v_isSharedCheck_5653_ =
                                                    (!lean_is_exclusive(v___x_5619_)) as u8;
                                                if v_isSharedCheck_5653_ == 0 {
                                                    v___x_5648_ = v___x_5619_;
                                                    v_isShared_5649_ = v_isSharedCheck_5653_;
                                                    state = 70;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5646_);
                                                    lean_dec(v___x_5619_);
                                                    v___x_5648_ = lean_box(0);
                                                    v_isShared_5649_ = v_isSharedCheck_5653_;
                                                    state = 70;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_5226_);
                                        lean_dec_ref(v_item_5204_);
                                        lean_dec_ref(v_config_5203_);
                                        v_a_5654_ = lean_ctor_get(v___x_5617_, 0);
                                        v_isSharedCheck_5661_ =
                                            (!lean_is_exclusive(v___x_5617_)) as u8;
                                        if v_isSharedCheck_5661_ == 0 {
                                            v___x_5656_ = v___x_5617_;
                                            v_isShared_5657_ = v_isSharedCheck_5661_;
                                            state = 72;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5654_);
                                            lean_dec(v___x_5617_);
                                            v___x_5656_ = lean_box(0);
                                            v_isShared_5657_ = v_isSharedCheck_5661_;
                                            state = 72;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_5662_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19;
                                v___x_5663_ = lean_string_dec_eq(v___x_5225_, v___x_5662_);
                                if v___x_5663_ == 0 {
                                    v___x_5664_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20;
                                    v___x_5665_ = lean_string_dec_eq(v___x_5225_, v___x_5664_);
                                    if v___x_5665_ == 0 {
                                        v___x_5666_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21;
                                        v___x_5667_ = lean_string_dec_eq(v___x_5225_, v___x_5666_);
                                        lean_dec_ref(v___x_5225_);
                                        if v___x_5667_ == 0 {
                                            lean_dec_ref(v_item_5204_);
                                            lean_dec_ref(v_config_5203_);
                                            v_item_5213_ = v___x_5226_;
                                            v___y_5214_ = v___y_5205_;
                                            v___y_5215_ = v___y_5206_;
                                            v___y_5216_ = v___y_5207_;
                                            v___y_5217_ = v___y_5208_;
                                            v___y_5218_ = v___y_5209_;
                                            v___y_5219_ = v___y_5210_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_5668_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22;
                                            v___x_5669_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                    v_item_5204_,
                                                    v___x_5668_,
                                                    v___y_5205_,
                                                    v___y_5206_,
                                                    v___y_5207_,
                                                    v___y_5208_,
                                                    v___y_5209_,
                                                    v___y_5210_,
                                                );
                                            if lean_obj_tag(v___x_5669_) == 0 {
                                                lean_dec_ref_known(v___x_5669_, 1);
                                                v___x_5670_ =
                                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                        v___x_5226_,
                                                    );
                                                if v___x_5670_ == 0 {
                                                    lean_dec_ref(v_item_5204_);
                                                    lean_dec_ref(v_config_5203_);
                                                    v_item_5213_ = v___x_5226_;
                                                    v___y_5214_ = v___y_5205_;
                                                    v___y_5215_ = v___y_5206_;
                                                    v___y_5216_ = v___y_5207_;
                                                    v___y_5217_ = v___y_5208_;
                                                    v___y_5218_ = v___y_5209_;
                                                    v___y_5219_ = v___y_5210_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec_ref(v___x_5226_);
                                                    v___x_5671_ =
                                                        l_Lean_Elab_ConfigEval_evalBoolItem(
                                                            v_item_5204_,
                                                            v___y_5205_,
                                                            v___y_5206_,
                                                            v___y_5207_,
                                                            v___y_5208_,
                                                            v___y_5209_,
                                                            v___y_5210_,
                                                        );
                                                    if lean_obj_tag(v___x_5671_) == 0 {
                                                        v_a_5672_ = lean_ctor_get(v___x_5671_, 0);
                                                        v_isSharedCheck_5697_ =
                                                            (!lean_is_exclusive(v___x_5671_)) as u8;
                                                        if v_isSharedCheck_5697_ == 0 {
                                                            v___x_5674_ = v___x_5671_;
                                                            v_isShared_5675_ =
                                                                v_isSharedCheck_5697_;
                                                            state = 74;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_5672_);
                                                            lean_dec(v___x_5671_);
                                                            v___x_5674_ = lean_box(0);
                                                            v_isShared_5675_ =
                                                                v_isSharedCheck_5697_;
                                                            state = 74;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_config_5203_);
                                                        v_a_5698_ = lean_ctor_get(v___x_5671_, 0);
                                                        v_isSharedCheck_5705_ =
                                                            (!lean_is_exclusive(v___x_5671_)) as u8;
                                                        if v_isSharedCheck_5705_ == 0 {
                                                            v___x_5700_ = v___x_5671_;
                                                            v_isShared_5701_ =
                                                                v_isSharedCheck_5705_;
                                                            state = 78;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_5698_);
                                                            lean_dec(v___x_5671_);
                                                            v___x_5700_ = lean_box(0);
                                                            v_isShared_5701_ =
                                                                v_isSharedCheck_5705_;
                                                            state = 78;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_5226_);
                                                lean_dec_ref(v_item_5204_);
                                                lean_dec_ref(v_config_5203_);
                                                v_a_5706_ = lean_ctor_get(v___x_5669_, 0);
                                                v_isSharedCheck_5713_ =
                                                    (!lean_is_exclusive(v___x_5669_)) as u8;
                                                if v_isSharedCheck_5713_ == 0 {
                                                    v___x_5708_ = v___x_5669_;
                                                    v_isShared_5709_ = v_isSharedCheck_5713_;
                                                    state = 80;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5706_);
                                                    lean_dec(v___x_5669_);
                                                    v___x_5708_ = lean_box(0);
                                                    v_isShared_5709_ = v_isSharedCheck_5713_;
                                                    state = 80;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_5225_);
                                        v___x_5714_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23;
                                        v___x_5715_ =
                                            l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                v_item_5204_,
                                                v___x_5714_,
                                                v___y_5205_,
                                                v___y_5206_,
                                                v___y_5207_,
                                                v___y_5208_,
                                                v___y_5209_,
                                                v___y_5210_,
                                            );
                                        if lean_obj_tag(v___x_5715_) == 0 {
                                            lean_dec_ref_known(v___x_5715_, 1);
                                            v___x_5716_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                    v___x_5226_,
                                                );
                                            if v___x_5716_ == 0 {
                                                lean_dec_ref(v_item_5204_);
                                                lean_dec_ref(v_config_5203_);
                                                v_item_5213_ = v___x_5226_;
                                                v___y_5214_ = v___y_5205_;
                                                v___y_5215_ = v___y_5206_;
                                                v___y_5216_ = v___y_5207_;
                                                v___y_5217_ = v___y_5208_;
                                                v___y_5218_ = v___y_5209_;
                                                v___y_5219_ = v___y_5210_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec_ref(v___x_5226_);
                                                v___x_5717_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                    v_item_5204_,
                                                    v___y_5205_,
                                                    v___y_5206_,
                                                    v___y_5207_,
                                                    v___y_5208_,
                                                    v___y_5209_,
                                                    v___y_5210_,
                                                );
                                                if lean_obj_tag(v___x_5717_) == 0 {
                                                    v_a_5718_ = lean_ctor_get(v___x_5717_, 0);
                                                    v_isSharedCheck_5743_ =
                                                        (!lean_is_exclusive(v___x_5717_)) as u8;
                                                    if v_isSharedCheck_5743_ == 0 {
                                                        v___x_5720_ = v___x_5717_;
                                                        v_isShared_5721_ = v_isSharedCheck_5743_;
                                                        state = 82;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5718_);
                                                        lean_dec(v___x_5717_);
                                                        v___x_5720_ = lean_box(0);
                                                        v_isShared_5721_ = v_isSharedCheck_5743_;
                                                        state = 82;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_config_5203_);
                                                    v_a_5744_ = lean_ctor_get(v___x_5717_, 0);
                                                    v_isSharedCheck_5751_ =
                                                        (!lean_is_exclusive(v___x_5717_)) as u8;
                                                    if v_isSharedCheck_5751_ == 0 {
                                                        v___x_5746_ = v___x_5717_;
                                                        v_isShared_5747_ = v_isSharedCheck_5751_;
                                                        state = 86;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5744_);
                                                        lean_dec(v___x_5717_);
                                                        v___x_5746_ = lean_box(0);
                                                        v_isShared_5747_ = v_isSharedCheck_5751_;
                                                        state = 86;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_5226_);
                                            lean_dec_ref(v_item_5204_);
                                            lean_dec_ref(v_config_5203_);
                                            v_a_5752_ = lean_ctor_get(v___x_5715_, 0);
                                            v_isSharedCheck_5759_ =
                                                (!lean_is_exclusive(v___x_5715_)) as u8;
                                            if v_isSharedCheck_5759_ == 0 {
                                                v___x_5754_ = v___x_5715_;
                                                v_isShared_5755_ = v_isSharedCheck_5759_;
                                                state = 88;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5752_);
                                                lean_dec(v___x_5715_);
                                                v___x_5754_ = lean_box(0);
                                                v_isShared_5755_ = v_isSharedCheck_5759_;
                                                state = 88;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_5225_);
                                    lean_dec_ref(v_config_5203_);
                                    v___x_5760_ =
                                        l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_5226_);
                                    if v___x_5760_ == 0 {
                                        lean_dec_ref(v_item_5204_);
                                        v_item_5213_ = v___x_5226_;
                                        v___y_5214_ = v___y_5205_;
                                        v___y_5215_ = v___y_5206_;
                                        v___y_5216_ = v___y_5207_;
                                        v___y_5217_ = v___y_5208_;
                                        v___y_5218_ = v___y_5209_;
                                        v___y_5219_ = v___y_5210_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec_ref(v___x_5226_);
                                        v_value_5761_ = lean_ctor_get(v_item_5204_, 2);
                                        lean_inc(v_value_5761_);
                                        lean_dec_ref(v_item_5204_);
                                        v___x_5762_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0(v_value_5761_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_);
                                        return v___x_5762_;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_config_5203_);
                        v_item_5213_ = v_item_5204_;
                        v___y_5214_ = v___y_5205_;
                        v___y_5215_ = v___y_5206_;
                        v___y_5216_ = v___y_5207_;
                        v___y_5217_ = v___y_5208_;
                        v___y_5218_ = v___y_5209_;
                        v___y_5219_ = v___y_5210_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_item_5204_);
                    lean_dec_ref(v_config_5203_);
                    v_a_5763_ = lean_ctor_get(v___x_5223_, 0);
                    v_isSharedCheck_5770_ = (!lean_is_exclusive(v___x_5223_)) as u8;
                    if v_isSharedCheck_5770_ == 0 {
                        v___x_5765_ = v___x_5223_;
                        v_isShared_5766_ = v_isSharedCheck_5770_;
                        state = 90;
                        continue;
                    } else {
                        lean_inc(v_a_5763_);
                        lean_dec(v___x_5223_);
                        v___x_5765_ = lean_box(0);
                        v_isShared_5766_ = v_isSharedCheck_5770_;
                        state = 90;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5220_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__0;
                v___x_5221_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(
                    v_item_5213_,
                    v___x_5220_,
                    v___y_5214_,
                    v___y_5215_,
                    v___y_5216_,
                    v___y_5217_,
                    v___y_5218_,
                    v___y_5219_,
                );
                return v___x_5221_;
            }
            2 => {
                v_proofs_5244_ = lean_ctor_get_uint8(v_config_5203_, 0 as u32);
                v_types_5245_ = lean_ctor_get_uint8(v_config_5203_, 1 as u32);
                v_implicits_5246_ = lean_ctor_get_uint8(v_config_5203_, 2 as u32);
                v_descend_5247_ = lean_ctor_get_uint8(v_config_5203_, 3 as u32);
                v_underBinder_5248_ = lean_ctor_get_uint8(v_config_5203_, 4 as u32);
                v_merge_5249_ = lean_ctor_get_uint8(v_config_5203_, 6 as u32);
                v_useContext_5250_ = lean_ctor_get_uint8(v_config_5203_, 7 as u32);
                v_onlyGivenNames_5251_ = lean_ctor_get_uint8(v_config_5203_, 8 as u32);
                v_preserveBinderNames_5252_ = lean_ctor_get_uint8(v_config_5203_, 9 as u32);
                v_lift_5253_ = lean_ctor_get_uint8(v_config_5203_, 10 as u32);
                v_isSharedCheck_5264_ = (!lean_is_exclusive(v_config_5203_)) as u8;
                if v_isSharedCheck_5264_ == 0 {
                    v___x_5255_ = v_config_5203_;
                    v_isShared_5256_ = v_isSharedCheck_5264_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_config_5203_);
                    v___x_5255_ = lean_box(0);
                    v_isShared_5256_ = v_isSharedCheck_5264_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5256_ == 0 {
                    v___x_5258_ = v___x_5255_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5263_, 0 as u32, v_proofs_5244_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5263_, 1 as u32, v_types_5245_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5263_, 2 as u32, v_implicits_5246_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5263_, 3 as u32, v_descend_5247_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5263_, 4 as u32, v_underBinder_5248_);
                    v___x_5258_ = v_reuseFailAlloc_5263_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5259_ = (lean_unbox(v_a_5240_) as u8);
                lean_dec(v_a_5240_);
                lean_ctor_set_uint8(v___x_5258_, 5 as u32, v___x_5259_);
                lean_ctor_set_uint8(v___x_5258_, 6 as u32, v_merge_5249_);
                lean_ctor_set_uint8(v___x_5258_, 7 as u32, v_useContext_5250_);
                lean_ctor_set_uint8(v___x_5258_, 8 as u32, v_onlyGivenNames_5251_);
                lean_ctor_set_uint8(v___x_5258_, 9 as u32, v_preserveBinderNames_5252_);
                lean_ctor_set_uint8(v___x_5258_, 10 as u32, v_lift_5253_);
                if v_isShared_5243_ == 0 {
                    lean_ctor_set(v___x_5242_, 0, v___x_5258_);
                    v___x_5261_ = v___x_5242_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5262_, 0, v___x_5258_);
                    v___x_5261_ = v_reuseFailAlloc_5262_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5261_;
            }
            6 => {
                if v_isShared_5269_ == 0 {
                    v___x_5271_ = v___x_5268_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5272_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
                    v___x_5271_ = v_reuseFailAlloc_5272_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5271_;
            }
            8 => {
                if v_isShared_5277_ == 0 {
                    v___x_5279_ = v___x_5276_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5280_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5274_);
                    v___x_5279_ = v_reuseFailAlloc_5280_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5279_;
            }
            10 => {
                v_proofs_5290_ = lean_ctor_get_uint8(v_config_5203_, 0 as u32);
                v_types_5291_ = lean_ctor_get_uint8(v_config_5203_, 1 as u32);
                v_implicits_5292_ = lean_ctor_get_uint8(v_config_5203_, 2 as u32);
                v_descend_5293_ = lean_ctor_get_uint8(v_config_5203_, 3 as u32);
                v_underBinder_5294_ = lean_ctor_get_uint8(v_config_5203_, 4 as u32);
                v_usedOnly_5295_ = lean_ctor_get_uint8(v_config_5203_, 5 as u32);
                v_merge_5296_ = lean_ctor_get_uint8(v_config_5203_, 6 as u32);
                v_onlyGivenNames_5297_ = lean_ctor_get_uint8(v_config_5203_, 8 as u32);
                v_preserveBinderNames_5298_ = lean_ctor_get_uint8(v_config_5203_, 9 as u32);
                v_lift_5299_ = lean_ctor_get_uint8(v_config_5203_, 10 as u32);
                v_isSharedCheck_5310_ = (!lean_is_exclusive(v_config_5203_)) as u8;
                if v_isSharedCheck_5310_ == 0 {
                    v___x_5301_ = v_config_5203_;
                    v_isShared_5302_ = v_isSharedCheck_5310_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_config_5203_);
                    v___x_5301_ = lean_box(0);
                    v_isShared_5302_ = v_isSharedCheck_5310_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5302_ == 0 {
                    v___x_5304_ = v___x_5301_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5309_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5309_, 0 as u32, v_proofs_5290_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5309_, 1 as u32, v_types_5291_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5309_, 2 as u32, v_implicits_5292_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5309_, 3 as u32, v_descend_5293_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5309_, 4 as u32, v_underBinder_5294_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5309_, 5 as u32, v_usedOnly_5295_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5309_, 6 as u32, v_merge_5296_);
                    v___x_5304_ = v_reuseFailAlloc_5309_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5305_ = (lean_unbox(v_a_5286_) as u8);
                lean_dec(v_a_5286_);
                lean_ctor_set_uint8(v___x_5304_, 7 as u32, v___x_5305_);
                lean_ctor_set_uint8(v___x_5304_, 8 as u32, v_onlyGivenNames_5297_);
                lean_ctor_set_uint8(v___x_5304_, 9 as u32, v_preserveBinderNames_5298_);
                lean_ctor_set_uint8(v___x_5304_, 10 as u32, v_lift_5299_);
                if v_isShared_5289_ == 0 {
                    lean_ctor_set(v___x_5288_, 0, v___x_5304_);
                    v___x_5307_ = v___x_5288_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5308_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5308_, 0, v___x_5304_);
                    v___x_5307_ = v_reuseFailAlloc_5308_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5307_;
            }
            14 => {
                if v_isShared_5315_ == 0 {
                    v___x_5317_ = v___x_5314_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_a_5312_);
                    v___x_5317_ = v_reuseFailAlloc_5318_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5317_;
            }
            16 => {
                if v_isShared_5323_ == 0 {
                    v___x_5325_ = v___x_5322_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5326_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5326_, 0, v_a_5320_);
                    v___x_5325_ = v_reuseFailAlloc_5326_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5325_;
            }
            18 => {
                v_proofs_5336_ = lean_ctor_get_uint8(v_config_5203_, 0 as u32);
                v_types_5337_ = lean_ctor_get_uint8(v_config_5203_, 1 as u32);
                v_implicits_5338_ = lean_ctor_get_uint8(v_config_5203_, 2 as u32);
                v_descend_5339_ = lean_ctor_get_uint8(v_config_5203_, 3 as u32);
                v_usedOnly_5340_ = lean_ctor_get_uint8(v_config_5203_, 5 as u32);
                v_merge_5341_ = lean_ctor_get_uint8(v_config_5203_, 6 as u32);
                v_useContext_5342_ = lean_ctor_get_uint8(v_config_5203_, 7 as u32);
                v_onlyGivenNames_5343_ = lean_ctor_get_uint8(v_config_5203_, 8 as u32);
                v_preserveBinderNames_5344_ = lean_ctor_get_uint8(v_config_5203_, 9 as u32);
                v_lift_5345_ = lean_ctor_get_uint8(v_config_5203_, 10 as u32);
                v_isSharedCheck_5356_ = (!lean_is_exclusive(v_config_5203_)) as u8;
                if v_isSharedCheck_5356_ == 0 {
                    v___x_5347_ = v_config_5203_;
                    v_isShared_5348_ = v_isSharedCheck_5356_;
                    state = 19;
                    continue;
                } else {
                    lean_dec(v_config_5203_);
                    v___x_5347_ = lean_box(0);
                    v_isShared_5348_ = v_isSharedCheck_5356_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_5348_ == 0 {
                    v___x_5350_ = v___x_5347_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5355_, 0 as u32, v_proofs_5336_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5355_, 1 as u32, v_types_5337_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5355_, 2 as u32, v_implicits_5338_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5355_, 3 as u32, v_descend_5339_);
                    v___x_5350_ = v_reuseFailAlloc_5355_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_5351_ = (lean_unbox(v_a_5332_) as u8);
                lean_dec(v_a_5332_);
                lean_ctor_set_uint8(v___x_5350_, 4 as u32, v___x_5351_);
                lean_ctor_set_uint8(v___x_5350_, 5 as u32, v_usedOnly_5340_);
                lean_ctor_set_uint8(v___x_5350_, 6 as u32, v_merge_5341_);
                lean_ctor_set_uint8(v___x_5350_, 7 as u32, v_useContext_5342_);
                lean_ctor_set_uint8(v___x_5350_, 8 as u32, v_onlyGivenNames_5343_);
                lean_ctor_set_uint8(v___x_5350_, 9 as u32, v_preserveBinderNames_5344_);
                lean_ctor_set_uint8(v___x_5350_, 10 as u32, v_lift_5345_);
                if v_isShared_5335_ == 0 {
                    lean_ctor_set(v___x_5334_, 0, v___x_5350_);
                    v___x_5353_ = v___x_5334_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5354_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5354_, 0, v___x_5350_);
                    v___x_5353_ = v_reuseFailAlloc_5354_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5353_;
            }
            22 => {
                if v_isShared_5361_ == 0 {
                    v___x_5363_ = v___x_5360_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
                    v___x_5363_ = v_reuseFailAlloc_5364_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_5363_;
            }
            24 => {
                if v_isShared_5369_ == 0 {
                    v___x_5371_ = v___x_5368_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5372_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_a_5366_);
                    v___x_5371_ = v_reuseFailAlloc_5372_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_5371_;
            }
            26 => {
                v_proofs_5387_ = lean_ctor_get_uint8(v_config_5203_, 0 as u32);
                v_implicits_5388_ = lean_ctor_get_uint8(v_config_5203_, 2 as u32);
                v_descend_5389_ = lean_ctor_get_uint8(v_config_5203_, 3 as u32);
                v_underBinder_5390_ = lean_ctor_get_uint8(v_config_5203_, 4 as u32);
                v_usedOnly_5391_ = lean_ctor_get_uint8(v_config_5203_, 5 as u32);
                v_merge_5392_ = lean_ctor_get_uint8(v_config_5203_, 6 as u32);
                v_useContext_5393_ = lean_ctor_get_uint8(v_config_5203_, 7 as u32);
                v_onlyGivenNames_5394_ = lean_ctor_get_uint8(v_config_5203_, 8 as u32);
                v_preserveBinderNames_5395_ = lean_ctor_get_uint8(v_config_5203_, 9 as u32);
                v_lift_5396_ = lean_ctor_get_uint8(v_config_5203_, 10 as u32);
                v_isSharedCheck_5407_ = (!lean_is_exclusive(v_config_5203_)) as u8;
                if v_isSharedCheck_5407_ == 0 {
                    v___x_5398_ = v_config_5203_;
                    v_isShared_5399_ = v_isSharedCheck_5407_;
                    state = 27;
                    continue;
                } else {
                    lean_dec(v_config_5203_);
                    v___x_5398_ = lean_box(0);
                    v_isShared_5399_ = v_isSharedCheck_5407_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_5399_ == 0 {
                    v___x_5401_ = v___x_5398_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5406_, 0 as u32, v_proofs_5387_);
                    v___x_5401_ = v_reuseFailAlloc_5406_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_5402_ = (lean_unbox(v_a_5383_) as u8);
                lean_dec(v_a_5383_);
                lean_ctor_set_uint8(v___x_5401_, 1 as u32, v___x_5402_);
                lean_ctor_set_uint8(v___x_5401_, 2 as u32, v_implicits_5388_);
                lean_ctor_set_uint8(v___x_5401_, 3 as u32, v_descend_5389_);
                lean_ctor_set_uint8(v___x_5401_, 4 as u32, v_underBinder_5390_);
                lean_ctor_set_uint8(v___x_5401_, 5 as u32, v_usedOnly_5391_);
                lean_ctor_set_uint8(v___x_5401_, 6 as u32, v_merge_5392_);
                lean_ctor_set_uint8(v___x_5401_, 7 as u32, v_useContext_5393_);
                lean_ctor_set_uint8(v___x_5401_, 8 as u32, v_onlyGivenNames_5394_);
                lean_ctor_set_uint8(v___x_5401_, 9 as u32, v_preserveBinderNames_5395_);
                lean_ctor_set_uint8(v___x_5401_, 10 as u32, v_lift_5396_);
                if v_isShared_5386_ == 0 {
                    lean_ctor_set(v___x_5385_, 0, v___x_5401_);
                    v___x_5404_ = v___x_5385_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5405_, 0, v___x_5401_);
                    v___x_5404_ = v_reuseFailAlloc_5405_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_5404_;
            }
            30 => {
                if v_isShared_5412_ == 0 {
                    v___x_5414_ = v___x_5411_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_5415_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_a_5409_);
                    v___x_5414_ = v_reuseFailAlloc_5415_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_5414_;
            }
            32 => {
                if v_isShared_5420_ == 0 {
                    v___x_5422_ = v___x_5419_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5423_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_a_5417_);
                    v___x_5422_ = v_reuseFailAlloc_5423_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_5422_;
            }
            34 => {
                v_types_5433_ = lean_ctor_get_uint8(v_config_5203_, 1 as u32);
                v_implicits_5434_ = lean_ctor_get_uint8(v_config_5203_, 2 as u32);
                v_descend_5435_ = lean_ctor_get_uint8(v_config_5203_, 3 as u32);
                v_underBinder_5436_ = lean_ctor_get_uint8(v_config_5203_, 4 as u32);
                v_usedOnly_5437_ = lean_ctor_get_uint8(v_config_5203_, 5 as u32);
                v_merge_5438_ = lean_ctor_get_uint8(v_config_5203_, 6 as u32);
                v_useContext_5439_ = lean_ctor_get_uint8(v_config_5203_, 7 as u32);
                v_onlyGivenNames_5440_ = lean_ctor_get_uint8(v_config_5203_, 8 as u32);
                v_preserveBinderNames_5441_ = lean_ctor_get_uint8(v_config_5203_, 9 as u32);
                v_lift_5442_ = lean_ctor_get_uint8(v_config_5203_, 10 as u32);
                v_isSharedCheck_5453_ = (!lean_is_exclusive(v_config_5203_)) as u8;
                if v_isSharedCheck_5453_ == 0 {
                    v___x_5444_ = v_config_5203_;
                    v_isShared_5445_ = v_isSharedCheck_5453_;
                    state = 35;
                    continue;
                } else {
                    lean_dec(v_config_5203_);
                    v___x_5444_ = lean_box(0);
                    v_isShared_5445_ = v_isSharedCheck_5453_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_5445_ == 0 {
                    v___x_5447_ = v___x_5444_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5452_ = lean_alloc_ctor(0, 0, (11) as u32);
                    v___x_5447_ = v_reuseFailAlloc_5452_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                v___x_5448_ = (lean_unbox(v_a_5429_) as u8);
                lean_dec(v_a_5429_);
                lean_ctor_set_uint8(v___x_5447_, 0 as u32, v___x_5448_);
                lean_ctor_set_uint8(v___x_5447_, 1 as u32, v_types_5433_);
                lean_ctor_set_uint8(v___x_5447_, 2 as u32, v_implicits_5434_);
                lean_ctor_set_uint8(v___x_5447_, 3 as u32, v_descend_5435_);
                lean_ctor_set_uint8(v___x_5447_, 4 as u32, v_underBinder_5436_);
                lean_ctor_set_uint8(v___x_5447_, 5 as u32, v_usedOnly_5437_);
                lean_ctor_set_uint8(v___x_5447_, 6 as u32, v_merge_5438_);
                lean_ctor_set_uint8(v___x_5447_, 7 as u32, v_useContext_5439_);
                lean_ctor_set_uint8(v___x_5447_, 8 as u32, v_onlyGivenNames_5440_);
                lean_ctor_set_uint8(v___x_5447_, 9 as u32, v_preserveBinderNames_5441_);
                lean_ctor_set_uint8(v___x_5447_, 10 as u32, v_lift_5442_);
                if v_isShared_5432_ == 0 {
                    lean_ctor_set(v___x_5431_, 0, v___x_5447_);
                    v___x_5450_ = v___x_5431_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_5451_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5451_, 0, v___x_5447_);
                    v___x_5450_ = v_reuseFailAlloc_5451_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_5450_;
            }
            38 => {
                if v_isShared_5458_ == 0 {
                    v___x_5460_ = v___x_5457_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_5461_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5455_);
                    v___x_5460_ = v_reuseFailAlloc_5461_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_5460_;
            }
            40 => {
                if v_isShared_5466_ == 0 {
                    v___x_5468_ = v___x_5465_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5469_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
                    v___x_5468_ = v_reuseFailAlloc_5469_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_5468_;
            }
            42 => {
                v_proofs_5479_ = lean_ctor_get_uint8(v_config_5203_, 0 as u32);
                v_types_5480_ = lean_ctor_get_uint8(v_config_5203_, 1 as u32);
                v_implicits_5481_ = lean_ctor_get_uint8(v_config_5203_, 2 as u32);
                v_descend_5482_ = lean_ctor_get_uint8(v_config_5203_, 3 as u32);
                v_underBinder_5483_ = lean_ctor_get_uint8(v_config_5203_, 4 as u32);
                v_usedOnly_5484_ = lean_ctor_get_uint8(v_config_5203_, 5 as u32);
                v_merge_5485_ = lean_ctor_get_uint8(v_config_5203_, 6 as u32);
                v_useContext_5486_ = lean_ctor_get_uint8(v_config_5203_, 7 as u32);
                v_onlyGivenNames_5487_ = lean_ctor_get_uint8(v_config_5203_, 8 as u32);
                v_lift_5488_ = lean_ctor_get_uint8(v_config_5203_, 10 as u32);
                v_isSharedCheck_5499_ = (!lean_is_exclusive(v_config_5203_)) as u8;
                if v_isSharedCheck_5499_ == 0 {
                    v___x_5490_ = v_config_5203_;
                    v_isShared_5491_ = v_isSharedCheck_5499_;
                    state = 43;
                    continue;
                } else {
                    lean_dec(v_config_5203_);
                    v___x_5490_ = lean_box(0);
                    v_isShared_5491_ = v_isSharedCheck_5499_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_5491_ == 0 {
                    v___x_5493_ = v___x_5490_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_5498_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5498_, 0 as u32, v_proofs_5479_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5498_, 1 as u32, v_types_5480_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5498_, 2 as u32, v_implicits_5481_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5498_, 3 as u32, v_descend_5482_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5498_, 4 as u32, v_underBinder_5483_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5498_, 5 as u32, v_usedOnly_5484_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5498_, 6 as u32, v_merge_5485_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5498_, 7 as u32, v_useContext_5486_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5498_, 8 as u32, v_onlyGivenNames_5487_);
                    v___x_5493_ = v_reuseFailAlloc_5498_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_5494_ = (lean_unbox(v_a_5475_) as u8);
                lean_dec(v_a_5475_);
                lean_ctor_set_uint8(v___x_5493_, 9 as u32, v___x_5494_);
                lean_ctor_set_uint8(v___x_5493_, 10 as u32, v_lift_5488_);
                if v_isShared_5478_ == 0 {
                    lean_ctor_set(v___x_5477_, 0, v___x_5493_);
                    v___x_5496_ = v___x_5477_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_5497_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5497_, 0, v___x_5493_);
                    v___x_5496_ = v_reuseFailAlloc_5497_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_5496_;
            }
            46 => {
                if v_isShared_5504_ == 0 {
                    v___x_5506_ = v___x_5503_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_5507_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5507_, 0, v_a_5501_);
                    v___x_5506_ = v_reuseFailAlloc_5507_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_5506_;
            }
            48 => {
                if v_isShared_5512_ == 0 {
                    v___x_5514_ = v___x_5511_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_5515_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_a_5509_);
                    v___x_5514_ = v_reuseFailAlloc_5515_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_5514_;
            }
            50 => {
                v_proofs_5532_ = lean_ctor_get_uint8(v_config_5203_, 0 as u32);
                v_types_5533_ = lean_ctor_get_uint8(v_config_5203_, 1 as u32);
                v_implicits_5534_ = lean_ctor_get_uint8(v_config_5203_, 2 as u32);
                v_descend_5535_ = lean_ctor_get_uint8(v_config_5203_, 3 as u32);
                v_underBinder_5536_ = lean_ctor_get_uint8(v_config_5203_, 4 as u32);
                v_usedOnly_5537_ = lean_ctor_get_uint8(v_config_5203_, 5 as u32);
                v_merge_5538_ = lean_ctor_get_uint8(v_config_5203_, 6 as u32);
                v_useContext_5539_ = lean_ctor_get_uint8(v_config_5203_, 7 as u32);
                v_preserveBinderNames_5540_ = lean_ctor_get_uint8(v_config_5203_, 9 as u32);
                v_lift_5541_ = lean_ctor_get_uint8(v_config_5203_, 10 as u32);
                v_isSharedCheck_5552_ = (!lean_is_exclusive(v_config_5203_)) as u8;
                if v_isSharedCheck_5552_ == 0 {
                    v___x_5543_ = v_config_5203_;
                    v_isShared_5544_ = v_isSharedCheck_5552_;
                    state = 51;
                    continue;
                } else {
                    lean_dec(v_config_5203_);
                    v___x_5543_ = lean_box(0);
                    v_isShared_5544_ = v_isSharedCheck_5552_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                if v_isShared_5544_ == 0 {
                    v___x_5546_ = v___x_5543_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5551_, 0 as u32, v_proofs_5532_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5551_, 1 as u32, v_types_5533_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5551_, 2 as u32, v_implicits_5534_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5551_, 3 as u32, v_descend_5535_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5551_, 4 as u32, v_underBinder_5536_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5551_, 5 as u32, v_usedOnly_5537_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5551_, 6 as u32, v_merge_5538_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5551_, 7 as u32, v_useContext_5539_);
                    v___x_5546_ = v_reuseFailAlloc_5551_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                v___x_5547_ = (lean_unbox(v_a_5528_) as u8);
                lean_dec(v_a_5528_);
                lean_ctor_set_uint8(v___x_5546_, 8 as u32, v___x_5547_);
                lean_ctor_set_uint8(v___x_5546_, 9 as u32, v_preserveBinderNames_5540_);
                lean_ctor_set_uint8(v___x_5546_, 10 as u32, v_lift_5541_);
                if v_isShared_5531_ == 0 {
                    lean_ctor_set(v___x_5530_, 0, v___x_5546_);
                    v___x_5549_ = v___x_5530_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5550_, 0, v___x_5546_);
                    v___x_5549_ = v_reuseFailAlloc_5550_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_5549_;
            }
            54 => {
                if v_isShared_5557_ == 0 {
                    v___x_5559_ = v___x_5556_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_5560_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5560_, 0, v_a_5554_);
                    v___x_5559_ = v_reuseFailAlloc_5560_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_5559_;
            }
            56 => {
                if v_isShared_5565_ == 0 {
                    v___x_5567_ = v___x_5564_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_5568_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_a_5562_);
                    v___x_5567_ = v_reuseFailAlloc_5568_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_5567_;
            }
            58 => {
                v_proofs_5578_ = lean_ctor_get_uint8(v_config_5203_, 0 as u32);
                v_types_5579_ = lean_ctor_get_uint8(v_config_5203_, 1 as u32);
                v_implicits_5580_ = lean_ctor_get_uint8(v_config_5203_, 2 as u32);
                v_descend_5581_ = lean_ctor_get_uint8(v_config_5203_, 3 as u32);
                v_underBinder_5582_ = lean_ctor_get_uint8(v_config_5203_, 4 as u32);
                v_usedOnly_5583_ = lean_ctor_get_uint8(v_config_5203_, 5 as u32);
                v_useContext_5584_ = lean_ctor_get_uint8(v_config_5203_, 7 as u32);
                v_onlyGivenNames_5585_ = lean_ctor_get_uint8(v_config_5203_, 8 as u32);
                v_preserveBinderNames_5586_ = lean_ctor_get_uint8(v_config_5203_, 9 as u32);
                v_lift_5587_ = lean_ctor_get_uint8(v_config_5203_, 10 as u32);
                v_isSharedCheck_5598_ = (!lean_is_exclusive(v_config_5203_)) as u8;
                if v_isSharedCheck_5598_ == 0 {
                    v___x_5589_ = v_config_5203_;
                    v_isShared_5590_ = v_isSharedCheck_5598_;
                    state = 59;
                    continue;
                } else {
                    lean_dec(v_config_5203_);
                    v___x_5589_ = lean_box(0);
                    v_isShared_5590_ = v_isSharedCheck_5598_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                if v_isShared_5590_ == 0 {
                    v___x_5592_ = v___x_5589_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5597_, 0 as u32, v_proofs_5578_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5597_, 1 as u32, v_types_5579_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5597_, 2 as u32, v_implicits_5580_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5597_, 3 as u32, v_descend_5581_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5597_, 4 as u32, v_underBinder_5582_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5597_, 5 as u32, v_usedOnly_5583_);
                    v___x_5592_ = v_reuseFailAlloc_5597_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_5593_ = (lean_unbox(v_a_5574_) as u8);
                lean_dec(v_a_5574_);
                lean_ctor_set_uint8(v___x_5592_, 6 as u32, v___x_5593_);
                lean_ctor_set_uint8(v___x_5592_, 7 as u32, v_useContext_5584_);
                lean_ctor_set_uint8(v___x_5592_, 8 as u32, v_onlyGivenNames_5585_);
                lean_ctor_set_uint8(v___x_5592_, 9 as u32, v_preserveBinderNames_5586_);
                lean_ctor_set_uint8(v___x_5592_, 10 as u32, v_lift_5587_);
                if v_isShared_5577_ == 0 {
                    lean_ctor_set(v___x_5576_, 0, v___x_5592_);
                    v___x_5595_ = v___x_5576_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5592_);
                    v___x_5595_ = v_reuseFailAlloc_5596_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_5595_;
            }
            62 => {
                if v_isShared_5603_ == 0 {
                    v___x_5605_ = v___x_5602_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_5606_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_a_5600_);
                    v___x_5605_ = v_reuseFailAlloc_5606_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_5605_;
            }
            64 => {
                if v_isShared_5611_ == 0 {
                    v___x_5613_ = v___x_5610_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_5614_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5614_, 0, v_a_5608_);
                    v___x_5613_ = v_reuseFailAlloc_5614_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_5613_;
            }
            66 => {
                v_proofs_5624_ = lean_ctor_get_uint8(v_config_5203_, 0 as u32);
                v_types_5625_ = lean_ctor_get_uint8(v_config_5203_, 1 as u32);
                v_implicits_5626_ = lean_ctor_get_uint8(v_config_5203_, 2 as u32);
                v_descend_5627_ = lean_ctor_get_uint8(v_config_5203_, 3 as u32);
                v_underBinder_5628_ = lean_ctor_get_uint8(v_config_5203_, 4 as u32);
                v_usedOnly_5629_ = lean_ctor_get_uint8(v_config_5203_, 5 as u32);
                v_merge_5630_ = lean_ctor_get_uint8(v_config_5203_, 6 as u32);
                v_useContext_5631_ = lean_ctor_get_uint8(v_config_5203_, 7 as u32);
                v_onlyGivenNames_5632_ = lean_ctor_get_uint8(v_config_5203_, 8 as u32);
                v_preserveBinderNames_5633_ = lean_ctor_get_uint8(v_config_5203_, 9 as u32);
                v_isSharedCheck_5644_ = (!lean_is_exclusive(v_config_5203_)) as u8;
                if v_isSharedCheck_5644_ == 0 {
                    v___x_5635_ = v_config_5203_;
                    v_isShared_5636_ = v_isSharedCheck_5644_;
                    state = 67;
                    continue;
                } else {
                    lean_dec(v_config_5203_);
                    v___x_5635_ = lean_box(0);
                    v_isShared_5636_ = v_isSharedCheck_5644_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                if v_isShared_5636_ == 0 {
                    v___x_5638_ = v___x_5635_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_5643_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5643_, 0 as u32, v_proofs_5624_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5643_, 1 as u32, v_types_5625_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5643_, 2 as u32, v_implicits_5626_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5643_, 3 as u32, v_descend_5627_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5643_, 4 as u32, v_underBinder_5628_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5643_, 5 as u32, v_usedOnly_5629_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5643_, 6 as u32, v_merge_5630_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5643_, 7 as u32, v_useContext_5631_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5643_, 8 as u32, v_onlyGivenNames_5632_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5643_,
                        9 as u32,
                        v_preserveBinderNames_5633_,
                    );
                    v___x_5638_ = v_reuseFailAlloc_5643_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                v___x_5639_ = (lean_unbox(v_a_5620_) as u8);
                lean_dec(v_a_5620_);
                lean_ctor_set_uint8(v___x_5638_, 10 as u32, v___x_5639_);
                if v_isShared_5623_ == 0 {
                    lean_ctor_set(v___x_5622_, 0, v___x_5638_);
                    v___x_5641_ = v___x_5622_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_5642_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5642_, 0, v___x_5638_);
                    v___x_5641_ = v_reuseFailAlloc_5642_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                return v___x_5641_;
            }
            70 => {
                if v_isShared_5649_ == 0 {
                    v___x_5651_ = v___x_5648_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_5652_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_a_5646_);
                    v___x_5651_ = v_reuseFailAlloc_5652_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                return v___x_5651_;
            }
            72 => {
                if v_isShared_5657_ == 0 {
                    v___x_5659_ = v___x_5656_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_5660_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_a_5654_);
                    v___x_5659_ = v_reuseFailAlloc_5660_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                return v___x_5659_;
            }
            74 => {
                v_proofs_5676_ = lean_ctor_get_uint8(v_config_5203_, 0 as u32);
                v_types_5677_ = lean_ctor_get_uint8(v_config_5203_, 1 as u32);
                v_descend_5678_ = lean_ctor_get_uint8(v_config_5203_, 3 as u32);
                v_underBinder_5679_ = lean_ctor_get_uint8(v_config_5203_, 4 as u32);
                v_usedOnly_5680_ = lean_ctor_get_uint8(v_config_5203_, 5 as u32);
                v_merge_5681_ = lean_ctor_get_uint8(v_config_5203_, 6 as u32);
                v_useContext_5682_ = lean_ctor_get_uint8(v_config_5203_, 7 as u32);
                v_onlyGivenNames_5683_ = lean_ctor_get_uint8(v_config_5203_, 8 as u32);
                v_preserveBinderNames_5684_ = lean_ctor_get_uint8(v_config_5203_, 9 as u32);
                v_lift_5685_ = lean_ctor_get_uint8(v_config_5203_, 10 as u32);
                v_isSharedCheck_5696_ = (!lean_is_exclusive(v_config_5203_)) as u8;
                if v_isSharedCheck_5696_ == 0 {
                    v___x_5687_ = v_config_5203_;
                    v_isShared_5688_ = v_isSharedCheck_5696_;
                    state = 75;
                    continue;
                } else {
                    lean_dec(v_config_5203_);
                    v___x_5687_ = lean_box(0);
                    v_isShared_5688_ = v_isSharedCheck_5696_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                if v_isShared_5688_ == 0 {
                    v___x_5690_ = v___x_5687_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_5695_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5695_, 0 as u32, v_proofs_5676_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5695_, 1 as u32, v_types_5677_);
                    v___x_5690_ = v_reuseFailAlloc_5695_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                v___x_5691_ = (lean_unbox(v_a_5672_) as u8);
                lean_dec(v_a_5672_);
                lean_ctor_set_uint8(v___x_5690_, 2 as u32, v___x_5691_);
                lean_ctor_set_uint8(v___x_5690_, 3 as u32, v_descend_5678_);
                lean_ctor_set_uint8(v___x_5690_, 4 as u32, v_underBinder_5679_);
                lean_ctor_set_uint8(v___x_5690_, 5 as u32, v_usedOnly_5680_);
                lean_ctor_set_uint8(v___x_5690_, 6 as u32, v_merge_5681_);
                lean_ctor_set_uint8(v___x_5690_, 7 as u32, v_useContext_5682_);
                lean_ctor_set_uint8(v___x_5690_, 8 as u32, v_onlyGivenNames_5683_);
                lean_ctor_set_uint8(v___x_5690_, 9 as u32, v_preserveBinderNames_5684_);
                lean_ctor_set_uint8(v___x_5690_, 10 as u32, v_lift_5685_);
                if v_isShared_5675_ == 0 {
                    lean_ctor_set(v___x_5674_, 0, v___x_5690_);
                    v___x_5693_ = v___x_5674_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_5694_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5694_, 0, v___x_5690_);
                    v___x_5693_ = v_reuseFailAlloc_5694_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                return v___x_5693_;
            }
            78 => {
                if v_isShared_5701_ == 0 {
                    v___x_5703_ = v___x_5700_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_5704_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5704_, 0, v_a_5698_);
                    v___x_5703_ = v_reuseFailAlloc_5704_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_5703_;
            }
            80 => {
                if v_isShared_5709_ == 0 {
                    v___x_5711_ = v___x_5708_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_5712_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5712_, 0, v_a_5706_);
                    v___x_5711_ = v_reuseFailAlloc_5712_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                return v___x_5711_;
            }
            82 => {
                v_proofs_5722_ = lean_ctor_get_uint8(v_config_5203_, 0 as u32);
                v_types_5723_ = lean_ctor_get_uint8(v_config_5203_, 1 as u32);
                v_implicits_5724_ = lean_ctor_get_uint8(v_config_5203_, 2 as u32);
                v_underBinder_5725_ = lean_ctor_get_uint8(v_config_5203_, 4 as u32);
                v_usedOnly_5726_ = lean_ctor_get_uint8(v_config_5203_, 5 as u32);
                v_merge_5727_ = lean_ctor_get_uint8(v_config_5203_, 6 as u32);
                v_useContext_5728_ = lean_ctor_get_uint8(v_config_5203_, 7 as u32);
                v_onlyGivenNames_5729_ = lean_ctor_get_uint8(v_config_5203_, 8 as u32);
                v_preserveBinderNames_5730_ = lean_ctor_get_uint8(v_config_5203_, 9 as u32);
                v_lift_5731_ = lean_ctor_get_uint8(v_config_5203_, 10 as u32);
                v_isSharedCheck_5742_ = (!lean_is_exclusive(v_config_5203_)) as u8;
                if v_isSharedCheck_5742_ == 0 {
                    v___x_5733_ = v_config_5203_;
                    v_isShared_5734_ = v_isSharedCheck_5742_;
                    state = 83;
                    continue;
                } else {
                    lean_dec(v_config_5203_);
                    v___x_5733_ = lean_box(0);
                    v_isShared_5734_ = v_isSharedCheck_5742_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_5734_ == 0 {
                    v___x_5736_ = v___x_5733_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_5741_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5741_, 0 as u32, v_proofs_5722_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5741_, 1 as u32, v_types_5723_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5741_, 2 as u32, v_implicits_5724_);
                    v___x_5736_ = v_reuseFailAlloc_5741_;
                    state = 84;
                    continue;
                }
            }
            84 => {
                v___x_5737_ = (lean_unbox(v_a_5718_) as u8);
                lean_dec(v_a_5718_);
                lean_ctor_set_uint8(v___x_5736_, 3 as u32, v___x_5737_);
                lean_ctor_set_uint8(v___x_5736_, 4 as u32, v_underBinder_5725_);
                lean_ctor_set_uint8(v___x_5736_, 5 as u32, v_usedOnly_5726_);
                lean_ctor_set_uint8(v___x_5736_, 6 as u32, v_merge_5727_);
                lean_ctor_set_uint8(v___x_5736_, 7 as u32, v_useContext_5728_);
                lean_ctor_set_uint8(v___x_5736_, 8 as u32, v_onlyGivenNames_5729_);
                lean_ctor_set_uint8(v___x_5736_, 9 as u32, v_preserveBinderNames_5730_);
                lean_ctor_set_uint8(v___x_5736_, 10 as u32, v_lift_5731_);
                if v_isShared_5721_ == 0 {
                    lean_ctor_set(v___x_5720_, 0, v___x_5736_);
                    v___x_5739_ = v___x_5720_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_5740_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5740_, 0, v___x_5736_);
                    v___x_5739_ = v_reuseFailAlloc_5740_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                return v___x_5739_;
            }
            86 => {
                if v_isShared_5747_ == 0 {
                    v___x_5749_ = v___x_5746_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_5750_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_a_5744_);
                    v___x_5749_ = v_reuseFailAlloc_5750_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                return v___x_5749_;
            }
            88 => {
                if v_isShared_5755_ == 0 {
                    v___x_5757_ = v___x_5754_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_5758_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5758_, 0, v_a_5752_);
                    v___x_5757_ = v_reuseFailAlloc_5758_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                return v___x_5757_;
            }
            90 => {
                if v_isShared_5766_ == 0 {
                    v___x_5768_ = v___x_5765_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_5769_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5769_, 0, v_a_5763_);
                    v___x_5768_ = v_reuseFailAlloc_5769_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_5768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___boxed(
    mut v_config_5771_: *mut LeanObject,
    mut v_item_5772_: *mut LeanObject,
    mut v___y_5773_: *mut LeanObject,
    mut v___y_5774_: *mut LeanObject,
    mut v___y_5775_: *mut LeanObject,
    mut v___y_5776_: *mut LeanObject,
    mut v___y_5777_: *mut LeanObject,
    mut v___y_5778_: *mut LeanObject,
    mut v___y_5779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5780_: *mut LeanObject = core::ptr::null_mut();
    v_res_5780_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0(v_config_5771_, v_item_5772_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_, v___y_5777_, v___y_5778_);
    lean_dec(v___y_5778_);
    lean_dec_ref(v___y_5777_);
    lean_dec(v___y_5776_);
    lean_dec_ref(v___y_5775_);
    lean_dec(v___y_5774_);
    lean_dec_ref(v___y_5773_);
    return v_res_5780_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0(
    mut v_e_5783_: *mut LeanObject,
    mut v___y_5784_: *mut LeanObject,
    mut v___y_5785_: *mut LeanObject,
    mut v___y_5786_: *mut LeanObject,
    mut v___y_5787_: *mut LeanObject,
    mut v___y_5788_: *mut LeanObject,
    mut v___y_5789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    v___x_5791_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_5783_, v___y_5787_);
    return v___x_5791_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___boxed(
    mut v_e_5792_: *mut LeanObject,
    mut v___y_5793_: *mut LeanObject,
    mut v___y_5794_: *mut LeanObject,
    mut v___y_5795_: *mut LeanObject,
    mut v___y_5796_: *mut LeanObject,
    mut v___y_5797_: *mut LeanObject,
    mut v___y_5798_: *mut LeanObject,
    mut v___y_5799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5800_: *mut LeanObject = core::ptr::null_mut();
    v_res_5800_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0(v_e_5792_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
    lean_dec(v___y_5798_);
    lean_dec_ref(v___y_5797_);
    lean_dec(v___y_5796_);
    lean_dec_ref(v___y_5795_);
    lean_dec(v___y_5794_);
    lean_dec_ref(v___y_5793_);
    return v_res_5800_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2(
    mut v_00_u03b1_5801_: *mut LeanObject,
    mut v___y_5802_: *mut LeanObject,
    mut v___y_5803_: *mut LeanObject,
    mut v___y_5804_: *mut LeanObject,
    mut v___y_5805_: *mut LeanObject,
    mut v___y_5806_: *mut LeanObject,
    mut v___y_5807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    v___x_5809_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
    return v___x_5809_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___boxed(
    mut v_00_u03b1_5810_: *mut LeanObject,
    mut v___y_5811_: *mut LeanObject,
    mut v___y_5812_: *mut LeanObject,
    mut v___y_5813_: *mut LeanObject,
    mut v___y_5814_: *mut LeanObject,
    mut v___y_5815_: *mut LeanObject,
    mut v___y_5816_: *mut LeanObject,
    mut v___y_5817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5818_: *mut LeanObject = core::ptr::null_mut();
    v_res_5818_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_);
    lean_dec(v___y_5816_);
    lean_dec_ref(v___y_5815_);
    lean_dec(v___y_5814_);
    lean_dec_ref(v___y_5813_);
    lean_dec(v___y_5812_);
    lean_dec_ref(v___y_5811_);
    return v_res_5818_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1(
    mut v_00_u03b1_5819_: *mut LeanObject,
    mut v_msg_5820_: *mut LeanObject,
    mut v___y_5821_: *mut LeanObject,
    mut v___y_5822_: *mut LeanObject,
    mut v___y_5823_: *mut LeanObject,
    mut v___y_5824_: *mut LeanObject,
    mut v___y_5825_: *mut LeanObject,
    mut v___y_5826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    v___x_5828_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_);
    return v___x_5828_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___boxed(
    mut v_00_u03b1_5829_: *mut LeanObject,
    mut v_msg_5830_: *mut LeanObject,
    mut v___y_5831_: *mut LeanObject,
    mut v___y_5832_: *mut LeanObject,
    mut v___y_5833_: *mut LeanObject,
    mut v___y_5834_: *mut LeanObject,
    mut v___y_5835_: *mut LeanObject,
    mut v___y_5836_: *mut LeanObject,
    mut v___y_5837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5838_: *mut LeanObject = core::ptr::null_mut();
    v_res_5838_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_5829_, v_msg_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_);
    lean_dec(v___y_5836_);
    lean_dec_ref(v___y_5835_);
    lean_dec(v___y_5834_);
    lean_dec_ref(v___y_5833_);
    lean_dec(v___y_5832_);
    lean_dec_ref(v___y_5831_);
    return v_res_5838_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2(
    mut v_msgData_5839_: *mut LeanObject,
    mut v_macroStack_5840_: *mut LeanObject,
    mut v___y_5841_: *mut LeanObject,
    mut v___y_5842_: *mut LeanObject,
    mut v___y_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
    mut v___y_5845_: *mut LeanObject,
    mut v___y_5846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    v___x_5848_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_5839_, v_macroStack_5840_, v___y_5845_);
    return v___x_5848_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(
    mut v_msgData_5849_: *mut LeanObject,
    mut v_macroStack_5850_: *mut LeanObject,
    mut v___y_5851_: *mut LeanObject,
    mut v___y_5852_: *mut LeanObject,
    mut v___y_5853_: *mut LeanObject,
    mut v___y_5854_: *mut LeanObject,
    mut v___y_5855_: *mut LeanObject,
    mut v___y_5856_: *mut LeanObject,
    mut v___y_5857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5858_: *mut LeanObject = core::ptr::null_mut();
    v_res_5858_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_5849_, v_macroStack_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_, v___y_5855_, v___y_5856_);
    lean_dec(v___y_5856_);
    lean_dec_ref(v___y_5855_);
    lean_dec(v___y_5854_);
    lean_dec_ref(v___y_5853_);
    lean_dec(v___y_5852_);
    lean_dec_ref(v___y_5851_);
    return v_res_5858_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    v___x_5859_ = lean_box(0);
    v___x_5860_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___closed__3;
    v___x_5861_ = l_Lean_mkConst(v___x_5860_, v___x_5859_);
    return v___x_5861_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    v___x_5862_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__0,
    );
    v___x_5863_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5863_, 0, v___x_5862_);
    return v___x_5863_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0(
    mut v_cfg_5864_: *mut LeanObject,
    mut v_cfgItem_5865_: *mut LeanObject,
    mut v___y_5866_: *mut LeanObject,
    mut v___y_5867_: *mut LeanObject,
    mut v___y_5868_: *mut LeanObject,
    mut v___y_5869_: *mut LeanObject,
    mut v___y_5870_: *mut LeanObject,
    mut v___y_5871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    v___x_5873_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___closed__1,
    );
    v___x_5874_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(
        v_cfg_5864_,
        v_cfgItem_5865_,
        v___x_5873_,
        v___y_5866_,
        v___y_5867_,
        v___y_5868_,
        v___y_5869_,
        v___y_5870_,
        v___y_5871_,
    );
    return v___x_5874_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0___boxed(
    mut v_cfg_5875_: *mut LeanObject,
    mut v_cfgItem_5876_: *mut LeanObject,
    mut v___y_5877_: *mut LeanObject,
    mut v___y_5878_: *mut LeanObject,
    mut v___y_5879_: *mut LeanObject,
    mut v___y_5880_: *mut LeanObject,
    mut v___y_5881_: *mut LeanObject,
    mut v___y_5882_: *mut LeanObject,
    mut v___y_5883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5884_: *mut LeanObject = core::ptr::null_mut();
    v_res_5884_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___lam__0(
        v_cfg_5875_,
        v_cfgItem_5876_,
        v___y_5877_,
        v___y_5878_,
        v___y_5879_,
        v___y_5880_,
        v___y_5881_,
        v___y_5882_,
    );
    lean_dec(v___y_5882_);
    lean_dec_ref(v___y_5881_);
    lean_dec(v___y_5880_);
    lean_dec_ref(v___y_5879_);
    lean_dec(v___y_5878_);
    lean_dec_ref(v___y_5877_);
    lean_dec(v_cfgItem_5876_);
    return v_res_5884_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(
    mut v_cfg_5886_: *mut LeanObject,
    mut v_init_5887_: *mut LeanObject,
    mut v_logExceptions_5888_: u8,
    mut v_a_5889_: *mut LeanObject,
    mut v_a_5890_: *mut LeanObject,
    mut v_a_5891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_onErr_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eval_5894_: *mut LeanObject = core::ptr::null_mut();
    v_onErr_5893_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0;
    v_eval_5894_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___closed__0;
    if v_logExceptions_5888_ == 0 {
        let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
        v___x_5895_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
            v_eval_5894_,
            v_init_5887_,
            v_cfg_5886_,
            v_onErr_5893_,
            v_logExceptions_5888_,
            v_a_5890_,
            v_a_5891_,
        );
        return v___x_5895_;
    } else {
        let mut v_recover_5896_: u8 = 0;
        let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
        v_recover_5896_ = lean_ctor_get_uint8(
            v_a_5889_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        );
        v___x_5897_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
            v_eval_5894_,
            v_init_5887_,
            v_cfg_5886_,
            v_onErr_5893_,
            v_recover_5896_,
            v_a_5890_,
            v_a_5891_,
        );
        return v___x_5897_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___boxed(
    mut v_cfg_5898_: *mut LeanObject,
    mut v_init_5899_: *mut LeanObject,
    mut v_logExceptions_5900_: *mut LeanObject,
    mut v_a_5901_: *mut LeanObject,
    mut v_a_5902_: *mut LeanObject,
    mut v_a_5903_: *mut LeanObject,
    mut v_a_5904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_5905_: u8 = 0;
    let mut v_res_5906_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_5905_ = (lean_unbox(v_logExceptions_5900_) as u8);
    v_res_5906_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(
        v_cfg_5898_,
        v_init_5899_,
        v_logExceptions_boxed_5905_,
        v_a_5901_,
        v_a_5902_,
        v_a_5903_,
    );
    lean_dec(v_a_5903_);
    lean_dec_ref(v_a_5902_);
    lean_dec_ref(v_a_5901_);
    return v_res_5906_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabExtractLetsConfig(
    mut v_cfg_5907_: *mut LeanObject,
    mut v_init_5908_: *mut LeanObject,
    mut v_logExceptions_5909_: u8,
    mut v_a_5910_: *mut LeanObject,
    mut v_a_5911_: *mut LeanObject,
    mut v_a_5912_: *mut LeanObject,
    mut v_a_5913_: *mut LeanObject,
    mut v_a_5914_: *mut LeanObject,
    mut v_a_5915_: *mut LeanObject,
    mut v_a_5916_: *mut LeanObject,
    mut v_a_5917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    v___x_5919_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(
        v_cfg_5907_,
        v_init_5908_,
        v_logExceptions_5909_,
        v_a_5910_,
        v_a_5916_,
        v_a_5917_,
    );
    return v___x_5919_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabExtractLetsConfig___boxed(
    mut v_cfg_5920_: *mut LeanObject,
    mut v_init_5921_: *mut LeanObject,
    mut v_logExceptions_5922_: *mut LeanObject,
    mut v_a_5923_: *mut LeanObject,
    mut v_a_5924_: *mut LeanObject,
    mut v_a_5925_: *mut LeanObject,
    mut v_a_5926_: *mut LeanObject,
    mut v_a_5927_: *mut LeanObject,
    mut v_a_5928_: *mut LeanObject,
    mut v_a_5929_: *mut LeanObject,
    mut v_a_5930_: *mut LeanObject,
    mut v_a_5931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_5932_: u8 = 0;
    let mut v_res_5933_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_5932_ = (lean_unbox(v_logExceptions_5922_) as u8);
    v_res_5933_ = l_Lean_Elab_Tactic_elabExtractLetsConfig(
        v_cfg_5920_,
        v_init_5921_,
        v_logExceptions_boxed_5932_,
        v_a_5923_,
        v_a_5924_,
        v_a_5925_,
        v_a_5926_,
        v_a_5927_,
        v_a_5928_,
        v_a_5929_,
        v_a_5930_,
    );
    lean_dec(v_a_5930_);
    lean_dec_ref(v_a_5929_);
    lean_dec(v_a_5928_);
    lean_dec_ref(v_a_5927_);
    lean_dec(v_a_5926_);
    lean_dec_ref(v_a_5925_);
    lean_dec(v_a_5924_);
    lean_dec_ref(v_a_5923_);
    return v_res_5933_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    v___x_5934_ = lean_box(0);
    v___x_5935_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_5936_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5936_, 0, v___x_5935_);
    lean_ctor_set(v___x_5936_, 1, v___x_5934_);
    return v___x_5936_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    v___x_5938_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0);
    v___x_5939_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5939_, 0, v___x_5938_);
    return v___x_5939_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___boxed(
    mut v___y_5940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5941_: *mut LeanObject = core::ptr::null_mut();
    v_res_5941_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
    return v_res_5941_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(
    mut v_00_u03b1_5942_: *mut LeanObject,
    mut v___y_5943_: *mut LeanObject,
    mut v___y_5944_: *mut LeanObject,
    mut v___y_5945_: *mut LeanObject,
    mut v___y_5946_: *mut LeanObject,
    mut v___y_5947_: *mut LeanObject,
    mut v___y_5948_: *mut LeanObject,
    mut v___y_5949_: *mut LeanObject,
    mut v___y_5950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    v___x_5952_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
    return v___x_5952_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___boxed(
    mut v_00_u03b1_5953_: *mut LeanObject,
    mut v___y_5954_: *mut LeanObject,
    mut v___y_5955_: *mut LeanObject,
    mut v___y_5956_: *mut LeanObject,
    mut v___y_5957_: *mut LeanObject,
    mut v___y_5958_: *mut LeanObject,
    mut v___y_5959_: *mut LeanObject,
    mut v___y_5960_: *mut LeanObject,
    mut v___y_5961_: *mut LeanObject,
    mut v___y_5962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5963_: *mut LeanObject = core::ptr::null_mut();
    v_res_5963_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(
            v_00_u03b1_5953_,
            v___y_5954_,
            v___y_5955_,
            v___y_5956_,
            v___y_5957_,
            v___y_5958_,
            v___y_5959_,
            v___y_5960_,
            v___y_5961_,
        );
    lean_dec(v___y_5961_);
    lean_dec_ref(v___y_5960_);
    lean_dec(v___y_5959_);
    lean_dec_ref(v___y_5958_);
    lean_dec(v___y_5957_);
    lean_dec_ref(v___y_5956_);
    lean_dec(v___y_5955_);
    lean_dec_ref(v___y_5954_);
    return v_res_5963_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(
    mut v_msg_5964_: *mut LeanObject,
    mut v___y_5965_: *mut LeanObject,
    mut v___y_5966_: *mut LeanObject,
    mut v___y_5967_: *mut LeanObject,
    mut v___y_5968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5975_: u8 = 0;
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5970_ = lean_ctor_get(v___y_5967_, 5);
                v___x_5971_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_);
                v_a_5972_ = lean_ctor_get(v___x_5971_, 0);
                v_isSharedCheck_5980_ = (!lean_is_exclusive(v___x_5971_)) as u8;
                if v_isSharedCheck_5980_ == 0 {
                    v___x_5974_ = v___x_5971_;
                    v_isShared_5975_ = v_isSharedCheck_5980_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5972_);
                    lean_dec(v___x_5971_);
                    v___x_5974_ = lean_box(0);
                    v_isShared_5975_ = v_isSharedCheck_5980_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5970_);
                v___x_5976_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5976_, 0, v_ref_5970_);
                lean_ctor_set(v___x_5976_, 1, v_a_5972_);
                if v_isShared_5975_ == 0 {
                    lean_ctor_set_tag(v___x_5974_, 1);
                    lean_ctor_set(v___x_5974_, 0, v___x_5976_);
                    v___x_5978_ = v___x_5974_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5979_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5979_, 0, v___x_5976_);
                    v___x_5978_ = v_reuseFailAlloc_5979_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___boxed(
    mut v_msg_5981_: *mut LeanObject,
    mut v___y_5982_: *mut LeanObject,
    mut v___y_5983_: *mut LeanObject,
    mut v___y_5984_: *mut LeanObject,
    mut v___y_5985_: *mut LeanObject,
    mut v___y_5986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5987_: *mut LeanObject = core::ptr::null_mut();
    v_res_5987_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(
        v_msg_5981_,
        v___y_5982_,
        v___y_5983_,
        v___y_5984_,
        v___y_5985_,
    );
    lean_dec(v___y_5985_);
    lean_dec_ref(v___y_5984_);
    lean_dec(v___y_5983_);
    lean_dec_ref(v___y_5982_);
    return v_res_5987_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    v___x_5989_ = l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0;
    v___x_5990_ = l_Lean_stringToMessageData(v___x_5989_);
    return v___x_5990_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExtractLets___lam__0(
    mut v_x_5991_: *mut LeanObject,
    mut v___y_5992_: *mut LeanObject,
    mut v___y_5993_: *mut LeanObject,
    mut v___y_5994_: *mut LeanObject,
    mut v___y_5995_: *mut LeanObject,
    mut v___y_5996_: *mut LeanObject,
    mut v___y_5997_: *mut LeanObject,
    mut v___y_5998_: *mut LeanObject,
    mut v___y_5999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    v___x_6001_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1,
    );
    v___x_6002_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(
        v___x_6001_,
        v___y_5996_,
        v___y_5997_,
        v___y_5998_,
        v___y_5999_,
    );
    return v___x_6002_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed(
    mut v_x_6003_: *mut LeanObject,
    mut v___y_6004_: *mut LeanObject,
    mut v___y_6005_: *mut LeanObject,
    mut v___y_6006_: *mut LeanObject,
    mut v___y_6007_: *mut LeanObject,
    mut v___y_6008_: *mut LeanObject,
    mut v___y_6009_: *mut LeanObject,
    mut v___y_6010_: *mut LeanObject,
    mut v___y_6011_: *mut LeanObject,
    mut v___y_6012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6013_: *mut LeanObject = core::ptr::null_mut();
    v_res_6013_ = l_Lean_Elab_Tactic_evalExtractLets___lam__0(
        v_x_6003_,
        v___y_6004_,
        v___y_6005_,
        v___y_6006_,
        v___y_6007_,
        v___y_6008_,
        v___y_6009_,
        v___y_6010_,
        v___y_6011_,
    );
    lean_dec(v___y_6011_);
    lean_dec_ref(v___y_6010_);
    lean_dec(v___y_6009_);
    lean_dec_ref(v___y_6008_);
    lean_dec(v___y_6007_);
    lean_dec_ref(v___y_6006_);
    lean_dec(v___y_6005_);
    lean_dec_ref(v___y_6004_);
    lean_dec(v_x_6003_);
    return v_res_6013_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExtractLets___lam__1(
    mut v_h_6014_: *mut LeanObject,
    mut v___x_6015_: *mut LeanObject,
    mut v_a_6016_: *mut LeanObject,
    mut v___y_6017_: *mut LeanObject,
    mut v___y_6018_: *mut LeanObject,
    mut v___y_6019_: *mut LeanObject,
    mut v___y_6020_: *mut LeanObject,
    mut v___y_6021_: *mut LeanObject,
    mut v___y_6022_: *mut LeanObject,
    mut v___y_6023_: *mut LeanObject,
    mut v___y_6024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6035_: u8 = 0;
    let mut v___x_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6042_: u8 = 0;
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6046_: u8 = 0;
    let mut v_unused_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6051_: u8 = 0;
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6055_: u8 = 0;
    let mut v_reuseFailAlloc_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6057_: u8 = 0;
    let mut v_unused_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6062_: u8 = 0;
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6066_: u8 = 0;
    let mut v_a_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6070_: u8 = 0;
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6026_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_6018_,
                    v___y_6021_,
                    v___y_6022_,
                    v___y_6023_,
                    v___y_6024_,
                );
                if lean_obj_tag(v___x_6026_) == 0 {
                    v_a_6027_ = lean_ctor_get(v___x_6026_, 0);
                    lean_inc(v_a_6027_);
                    lean_dec_ref_known(v___x_6026_, 1);
                    v___x_6028_ = l_Lean_MVarId_extractLetsLocalDecl(
                        v_a_6027_,
                        v_h_6014_,
                        v___x_6015_,
                        v_a_6016_,
                        v___y_6021_,
                        v___y_6022_,
                        v___y_6023_,
                        v___y_6024_,
                    );
                    if lean_obj_tag(v___x_6028_) == 0 {
                        v_a_6029_ = lean_ctor_get(v___x_6028_, 0);
                        lean_inc(v_a_6029_);
                        lean_dec_ref_known(v___x_6028_, 1);
                        v_fst_6030_ = lean_ctor_get(v_a_6029_, 0);
                        lean_inc(v_fst_6030_);
                        v_snd_6031_ = lean_ctor_get(v_a_6029_, 1);
                        lean_inc(v_snd_6031_);
                        lean_dec(v_a_6029_);
                        v_fst_6032_ = lean_ctor_get(v_fst_6030_, 0);
                        v_isSharedCheck_6057_ = (!lean_is_exclusive(v_fst_6030_)) as u8;
                        if v_isSharedCheck_6057_ == 0 {
                            v_unused_6058_ = lean_ctor_get(v_fst_6030_, 1);
                            lean_dec(v_unused_6058_);
                            v___x_6034_ = v_fst_6030_;
                            v_isShared_6035_ = v_isSharedCheck_6057_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_fst_6032_);
                            lean_dec(v_fst_6030_);
                            v___x_6034_ = lean_box(0);
                            v_isShared_6035_ = v_isSharedCheck_6057_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6059_ = lean_ctor_get(v___x_6028_, 0);
                        v_isSharedCheck_6066_ = (!lean_is_exclusive(v___x_6028_)) as u8;
                        if v_isSharedCheck_6066_ == 0 {
                            v___x_6061_ = v___x_6028_;
                            v_isShared_6062_ = v_isSharedCheck_6066_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6059_);
                            lean_dec(v___x_6028_);
                            v___x_6061_ = lean_box(0);
                            v_isShared_6062_ = v_isSharedCheck_6066_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_6016_);
                    lean_dec(v___x_6015_);
                    lean_dec(v_h_6014_);
                    v_a_6067_ = lean_ctor_get(v___x_6026_, 0);
                    v_isSharedCheck_6074_ = (!lean_is_exclusive(v___x_6026_)) as u8;
                    if v_isSharedCheck_6074_ == 0 {
                        v___x_6069_ = v___x_6026_;
                        v_isShared_6070_ = v_isSharedCheck_6074_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_6067_);
                        lean_dec(v___x_6026_);
                        v___x_6069_ = lean_box(0);
                        v_isShared_6070_ = v_isSharedCheck_6074_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6036_ = lean_box(0);
                if v_isShared_6035_ == 0 {
                    lean_ctor_set_tag(v___x_6034_, 1);
                    lean_ctor_set(v___x_6034_, 1, v___x_6036_);
                    lean_ctor_set(v___x_6034_, 0, v_snd_6031_);
                    v___x_6038_ = v___x_6034_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6056_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_snd_6031_);
                    lean_ctor_set(v_reuseFailAlloc_6056_, 1, v___x_6036_);
                    v___x_6038_ = v_reuseFailAlloc_6056_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6039_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_6038_,
                    v___y_6018_,
                    v___y_6021_,
                    v___y_6022_,
                    v___y_6023_,
                    v___y_6024_,
                );
                if lean_obj_tag(v___x_6039_) == 0 {
                    v_isSharedCheck_6046_ = (!lean_is_exclusive(v___x_6039_)) as u8;
                    if v_isSharedCheck_6046_ == 0 {
                        v_unused_6047_ = lean_ctor_get(v___x_6039_, 0);
                        lean_dec(v_unused_6047_);
                        v___x_6041_ = v___x_6039_;
                        v_isShared_6042_ = v_isSharedCheck_6046_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_6039_);
                        v___x_6041_ = lean_box(0);
                        v_isShared_6042_ = v_isSharedCheck_6046_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_6032_);
                    v_a_6048_ = lean_ctor_get(v___x_6039_, 0);
                    v_isSharedCheck_6055_ = (!lean_is_exclusive(v___x_6039_)) as u8;
                    if v_isSharedCheck_6055_ == 0 {
                        v___x_6050_ = v___x_6039_;
                        v_isShared_6051_ = v_isSharedCheck_6055_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6048_);
                        lean_dec(v___x_6039_);
                        v___x_6050_ = lean_box(0);
                        v_isShared_6051_ = v_isSharedCheck_6055_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6042_ == 0 {
                    lean_ctor_set(v___x_6041_, 0, v_fst_6032_);
                    v___x_6044_ = v___x_6041_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6045_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6045_, 0, v_fst_6032_);
                    v___x_6044_ = v_reuseFailAlloc_6045_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6044_;
            }
            5 => {
                if v_isShared_6051_ == 0 {
                    v___x_6053_ = v___x_6050_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6054_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6054_, 0, v_a_6048_);
                    v___x_6053_ = v_reuseFailAlloc_6054_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6053_;
            }
            7 => {
                if v_isShared_6062_ == 0 {
                    v___x_6064_ = v___x_6061_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6065_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_a_6059_);
                    v___x_6064_ = v_reuseFailAlloc_6065_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6064_;
            }
            9 => {
                if v_isShared_6070_ == 0 {
                    v___x_6072_ = v___x_6069_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6073_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6073_, 0, v_a_6067_);
                    v___x_6072_ = v_reuseFailAlloc_6073_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed(
    mut v_h_6075_: *mut LeanObject,
    mut v___x_6076_: *mut LeanObject,
    mut v_a_6077_: *mut LeanObject,
    mut v___y_6078_: *mut LeanObject,
    mut v___y_6079_: *mut LeanObject,
    mut v___y_6080_: *mut LeanObject,
    mut v___y_6081_: *mut LeanObject,
    mut v___y_6082_: *mut LeanObject,
    mut v___y_6083_: *mut LeanObject,
    mut v___y_6084_: *mut LeanObject,
    mut v___y_6085_: *mut LeanObject,
    mut v___y_6086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6087_: *mut LeanObject = core::ptr::null_mut();
    v_res_6087_ = l_Lean_Elab_Tactic_evalExtractLets___lam__1(
        v_h_6075_,
        v___x_6076_,
        v_a_6077_,
        v___y_6078_,
        v___y_6079_,
        v___y_6080_,
        v___y_6081_,
        v___y_6082_,
        v___y_6083_,
        v___y_6084_,
        v___y_6085_,
    );
    lean_dec(v___y_6085_);
    lean_dec_ref(v___y_6084_);
    lean_dec(v___y_6083_);
    lean_dec_ref(v___y_6082_);
    lean_dec(v___y_6081_);
    lean_dec_ref(v___y_6080_);
    lean_dec(v___y_6079_);
    lean_dec_ref(v___y_6078_);
    return v_res_6087_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExtractLets___lam__2(
    mut v___x_6088_: *mut LeanObject,
    mut v_a_6089_: *mut LeanObject,
    mut v_ids_6090_: *mut LeanObject,
    mut v_h_6091_: *mut LeanObject,
    mut v___y_6092_: *mut LeanObject,
    mut v___y_6093_: *mut LeanObject,
    mut v___y_6094_: *mut LeanObject,
    mut v___y_6095_: *mut LeanObject,
    mut v___y_6096_: *mut LeanObject,
    mut v___y_6097_: *mut LeanObject,
    mut v___y_6098_: *mut LeanObject,
    mut v___y_6099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6108_: u8 = 0;
    let mut v___x_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6101_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed as *mut core::ffi::c_void,
                    12,
                    3,
                );
                lean_closure_set(v___f_6101_, 0, v_h_6091_);
                lean_closure_set(v___f_6101_, 1, v___x_6088_);
                lean_closure_set(v___f_6101_, 2, v_a_6089_);
                v___x_6102_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___f_6101_,
                    v___y_6092_,
                    v___y_6093_,
                    v___y_6094_,
                    v___y_6095_,
                    v___y_6096_,
                    v___y_6097_,
                    v___y_6098_,
                    v___y_6099_,
                );
                if lean_obj_tag(v___x_6102_) == 0 {
                    v_a_6103_ = lean_ctor_get(v___x_6102_, 0);
                    lean_inc(v_a_6103_);
                    lean_dec_ref_known(v___x_6102_, 1);
                    v___x_6104_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(
                        v_ids_6090_,
                        v_a_6103_,
                        v___y_6092_,
                        v___y_6093_,
                        v___y_6094_,
                        v___y_6095_,
                        v___y_6096_,
                        v___y_6097_,
                        v___y_6098_,
                        v___y_6099_,
                    );
                    return v___x_6104_;
                } else {
                    lean_dec_ref(v_ids_6090_);
                    v_a_6105_ = lean_ctor_get(v___x_6102_, 0);
                    v_isSharedCheck_6112_ = (!lean_is_exclusive(v___x_6102_)) as u8;
                    if v_isSharedCheck_6112_ == 0 {
                        v___x_6107_ = v___x_6102_;
                        v_isShared_6108_ = v_isSharedCheck_6112_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6105_);
                        lean_dec(v___x_6102_);
                        v___x_6107_ = lean_box(0);
                        v_isShared_6108_ = v_isSharedCheck_6112_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6108_ == 0 {
                    v___x_6110_ = v___x_6107_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6111_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6111_, 0, v_a_6105_);
                    v___x_6110_ = v_reuseFailAlloc_6111_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed(
    mut v___x_6113_: *mut LeanObject,
    mut v_a_6114_: *mut LeanObject,
    mut v_ids_6115_: *mut LeanObject,
    mut v_h_6116_: *mut LeanObject,
    mut v___y_6117_: *mut LeanObject,
    mut v___y_6118_: *mut LeanObject,
    mut v___y_6119_: *mut LeanObject,
    mut v___y_6120_: *mut LeanObject,
    mut v___y_6121_: *mut LeanObject,
    mut v___y_6122_: *mut LeanObject,
    mut v___y_6123_: *mut LeanObject,
    mut v___y_6124_: *mut LeanObject,
    mut v___y_6125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6126_: *mut LeanObject = core::ptr::null_mut();
    v_res_6126_ = l_Lean_Elab_Tactic_evalExtractLets___lam__2(
        v___x_6113_,
        v_a_6114_,
        v_ids_6115_,
        v_h_6116_,
        v___y_6117_,
        v___y_6118_,
        v___y_6119_,
        v___y_6120_,
        v___y_6121_,
        v___y_6122_,
        v___y_6123_,
        v___y_6124_,
    );
    lean_dec(v___y_6124_);
    lean_dec_ref(v___y_6123_);
    lean_dec(v___y_6122_);
    lean_dec_ref(v___y_6121_);
    lean_dec(v___y_6120_);
    lean_dec_ref(v___y_6119_);
    lean_dec(v___y_6118_);
    lean_dec_ref(v___y_6117_);
    return v_res_6126_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExtractLets___lam__3(
    mut v___x_6127_: *mut LeanObject,
    mut v_a_6128_: *mut LeanObject,
    mut v___y_6129_: *mut LeanObject,
    mut v___y_6130_: *mut LeanObject,
    mut v___y_6131_: *mut LeanObject,
    mut v___y_6132_: *mut LeanObject,
    mut v___y_6133_: *mut LeanObject,
    mut v___y_6134_: *mut LeanObject,
    mut v___y_6135_: *mut LeanObject,
    mut v___y_6136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6147_: u8 = 0;
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6154_: u8 = 0;
    let mut v___x_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6158_: u8 = 0;
    let mut v_unused_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6163_: u8 = 0;
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6167_: u8 = 0;
    let mut v_reuseFailAlloc_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6169_: u8 = 0;
    let mut v_unused_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6174_: u8 = 0;
    let mut v___x_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6178_: u8 = 0;
    let mut v_a_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6182_: u8 = 0;
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6138_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_6130_,
                    v___y_6133_,
                    v___y_6134_,
                    v___y_6135_,
                    v___y_6136_,
                );
                if lean_obj_tag(v___x_6138_) == 0 {
                    v_a_6139_ = lean_ctor_get(v___x_6138_, 0);
                    lean_inc(v_a_6139_);
                    lean_dec_ref_known(v___x_6138_, 1);
                    v___x_6140_ = l_Lean_MVarId_extractLets(
                        v_a_6139_,
                        v___x_6127_,
                        v_a_6128_,
                        v___y_6133_,
                        v___y_6134_,
                        v___y_6135_,
                        v___y_6136_,
                    );
                    if lean_obj_tag(v___x_6140_) == 0 {
                        v_a_6141_ = lean_ctor_get(v___x_6140_, 0);
                        lean_inc(v_a_6141_);
                        lean_dec_ref_known(v___x_6140_, 1);
                        v_fst_6142_ = lean_ctor_get(v_a_6141_, 0);
                        lean_inc(v_fst_6142_);
                        v_snd_6143_ = lean_ctor_get(v_a_6141_, 1);
                        lean_inc(v_snd_6143_);
                        lean_dec(v_a_6141_);
                        v_fst_6144_ = lean_ctor_get(v_fst_6142_, 0);
                        v_isSharedCheck_6169_ = (!lean_is_exclusive(v_fst_6142_)) as u8;
                        if v_isSharedCheck_6169_ == 0 {
                            v_unused_6170_ = lean_ctor_get(v_fst_6142_, 1);
                            lean_dec(v_unused_6170_);
                            v___x_6146_ = v_fst_6142_;
                            v_isShared_6147_ = v_isSharedCheck_6169_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_fst_6144_);
                            lean_dec(v_fst_6142_);
                            v___x_6146_ = lean_box(0);
                            v_isShared_6147_ = v_isSharedCheck_6169_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6171_ = lean_ctor_get(v___x_6140_, 0);
                        v_isSharedCheck_6178_ = (!lean_is_exclusive(v___x_6140_)) as u8;
                        if v_isSharedCheck_6178_ == 0 {
                            v___x_6173_ = v___x_6140_;
                            v_isShared_6174_ = v_isSharedCheck_6178_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6171_);
                            lean_dec(v___x_6140_);
                            v___x_6173_ = lean_box(0);
                            v_isShared_6174_ = v_isSharedCheck_6178_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_6128_);
                    lean_dec(v___x_6127_);
                    v_a_6179_ = lean_ctor_get(v___x_6138_, 0);
                    v_isSharedCheck_6186_ = (!lean_is_exclusive(v___x_6138_)) as u8;
                    if v_isSharedCheck_6186_ == 0 {
                        v___x_6181_ = v___x_6138_;
                        v_isShared_6182_ = v_isSharedCheck_6186_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_6179_);
                        lean_dec(v___x_6138_);
                        v___x_6181_ = lean_box(0);
                        v_isShared_6182_ = v_isSharedCheck_6186_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6148_ = lean_box(0);
                if v_isShared_6147_ == 0 {
                    lean_ctor_set_tag(v___x_6146_, 1);
                    lean_ctor_set(v___x_6146_, 1, v___x_6148_);
                    lean_ctor_set(v___x_6146_, 0, v_snd_6143_);
                    v___x_6150_ = v___x_6146_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6168_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6168_, 0, v_snd_6143_);
                    lean_ctor_set(v_reuseFailAlloc_6168_, 1, v___x_6148_);
                    v___x_6150_ = v_reuseFailAlloc_6168_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6151_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_6150_,
                    v___y_6130_,
                    v___y_6133_,
                    v___y_6134_,
                    v___y_6135_,
                    v___y_6136_,
                );
                if lean_obj_tag(v___x_6151_) == 0 {
                    v_isSharedCheck_6158_ = (!lean_is_exclusive(v___x_6151_)) as u8;
                    if v_isSharedCheck_6158_ == 0 {
                        v_unused_6159_ = lean_ctor_get(v___x_6151_, 0);
                        lean_dec(v_unused_6159_);
                        v___x_6153_ = v___x_6151_;
                        v_isShared_6154_ = v_isSharedCheck_6158_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_6151_);
                        v___x_6153_ = lean_box(0);
                        v_isShared_6154_ = v_isSharedCheck_6158_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_6144_);
                    v_a_6160_ = lean_ctor_get(v___x_6151_, 0);
                    v_isSharedCheck_6167_ = (!lean_is_exclusive(v___x_6151_)) as u8;
                    if v_isSharedCheck_6167_ == 0 {
                        v___x_6162_ = v___x_6151_;
                        v_isShared_6163_ = v_isSharedCheck_6167_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6160_);
                        lean_dec(v___x_6151_);
                        v___x_6162_ = lean_box(0);
                        v_isShared_6163_ = v_isSharedCheck_6167_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6154_ == 0 {
                    lean_ctor_set(v___x_6153_, 0, v_fst_6144_);
                    v___x_6156_ = v___x_6153_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6157_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6157_, 0, v_fst_6144_);
                    v___x_6156_ = v_reuseFailAlloc_6157_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6156_;
            }
            5 => {
                if v_isShared_6163_ == 0 {
                    v___x_6165_ = v___x_6162_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6166_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_a_6160_);
                    v___x_6165_ = v_reuseFailAlloc_6166_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6165_;
            }
            7 => {
                if v_isShared_6174_ == 0 {
                    v___x_6176_ = v___x_6173_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6177_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6177_, 0, v_a_6171_);
                    v___x_6176_ = v_reuseFailAlloc_6177_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6176_;
            }
            9 => {
                if v_isShared_6182_ == 0 {
                    v___x_6184_ = v___x_6181_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6185_, 0, v_a_6179_);
                    v___x_6184_ = v_reuseFailAlloc_6185_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed(
    mut v___x_6187_: *mut LeanObject,
    mut v_a_6188_: *mut LeanObject,
    mut v___y_6189_: *mut LeanObject,
    mut v___y_6190_: *mut LeanObject,
    mut v___y_6191_: *mut LeanObject,
    mut v___y_6192_: *mut LeanObject,
    mut v___y_6193_: *mut LeanObject,
    mut v___y_6194_: *mut LeanObject,
    mut v___y_6195_: *mut LeanObject,
    mut v___y_6196_: *mut LeanObject,
    mut v___y_6197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6198_: *mut LeanObject = core::ptr::null_mut();
    v_res_6198_ = l_Lean_Elab_Tactic_evalExtractLets___lam__3(
        v___x_6187_,
        v_a_6188_,
        v___y_6189_,
        v___y_6190_,
        v___y_6191_,
        v___y_6192_,
        v___y_6193_,
        v___y_6194_,
        v___y_6195_,
        v___y_6196_,
    );
    lean_dec(v___y_6196_);
    lean_dec_ref(v___y_6195_);
    lean_dec(v___y_6194_);
    lean_dec_ref(v___y_6193_);
    lean_dec(v___y_6192_);
    lean_dec_ref(v___y_6191_);
    lean_dec(v___y_6190_);
    lean_dec_ref(v___y_6189_);
    return v_res_6198_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExtractLets___lam__4(
    mut v___f_6199_: *mut LeanObject,
    mut v_ids_6200_: *mut LeanObject,
    mut v___y_6201_: *mut LeanObject,
    mut v___y_6202_: *mut LeanObject,
    mut v___y_6203_: *mut LeanObject,
    mut v___y_6204_: *mut LeanObject,
    mut v___y_6205_: *mut LeanObject,
    mut v___y_6206_: *mut LeanObject,
    mut v___y_6207_: *mut LeanObject,
    mut v___y_6208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6216_: u8 = 0;
    let mut v___x_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6210_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___f_6199_,
                    v___y_6201_,
                    v___y_6202_,
                    v___y_6203_,
                    v___y_6204_,
                    v___y_6205_,
                    v___y_6206_,
                    v___y_6207_,
                    v___y_6208_,
                );
                if lean_obj_tag(v___x_6210_) == 0 {
                    v_a_6211_ = lean_ctor_get(v___x_6210_, 0);
                    lean_inc(v_a_6211_);
                    lean_dec_ref_known(v___x_6210_, 1);
                    v___x_6212_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(
                        v_ids_6200_,
                        v_a_6211_,
                        v___y_6201_,
                        v___y_6202_,
                        v___y_6203_,
                        v___y_6204_,
                        v___y_6205_,
                        v___y_6206_,
                        v___y_6207_,
                        v___y_6208_,
                    );
                    return v___x_6212_;
                } else {
                    lean_dec_ref(v_ids_6200_);
                    v_a_6213_ = lean_ctor_get(v___x_6210_, 0);
                    v_isSharedCheck_6220_ = (!lean_is_exclusive(v___x_6210_)) as u8;
                    if v_isSharedCheck_6220_ == 0 {
                        v___x_6215_ = v___x_6210_;
                        v_isShared_6216_ = v_isSharedCheck_6220_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6213_);
                        lean_dec(v___x_6210_);
                        v___x_6215_ = lean_box(0);
                        v_isShared_6216_ = v_isSharedCheck_6220_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6216_ == 0 {
                    v___x_6218_ = v___x_6215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6219_, 0, v_a_6213_);
                    v___x_6218_ = v_reuseFailAlloc_6219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed(
    mut v___f_6221_: *mut LeanObject,
    mut v_ids_6222_: *mut LeanObject,
    mut v___y_6223_: *mut LeanObject,
    mut v___y_6224_: *mut LeanObject,
    mut v___y_6225_: *mut LeanObject,
    mut v___y_6226_: *mut LeanObject,
    mut v___y_6227_: *mut LeanObject,
    mut v___y_6228_: *mut LeanObject,
    mut v___y_6229_: *mut LeanObject,
    mut v___y_6230_: *mut LeanObject,
    mut v___y_6231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6232_: *mut LeanObject = core::ptr::null_mut();
    v_res_6232_ = l_Lean_Elab_Tactic_evalExtractLets___lam__4(
        v___f_6221_,
        v_ids_6222_,
        v___y_6223_,
        v___y_6224_,
        v___y_6225_,
        v___y_6226_,
        v___y_6227_,
        v___y_6228_,
        v___y_6229_,
        v___y_6230_,
    );
    lean_dec(v___y_6230_);
    lean_dec_ref(v___y_6229_);
    lean_dec(v___y_6228_);
    lean_dec_ref(v___y_6227_);
    lean_dec(v___y_6226_);
    lean_dec_ref(v___y_6225_);
    lean_dec(v___y_6224_);
    lean_dec_ref(v___y_6223_);
    return v_res_6232_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(
    mut v_sz_6233_: usize,
    mut v_i_6234_: usize,
    mut v_bs_6235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6236_: u8 = 0;
    let mut v_v_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: usize = 0;
    let mut v___x_6242_: usize = 0;
    let mut v___x_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6236_ = lean_usize_dec_lt(v_i_6234_, v_sz_6233_);
                if v___x_6236_ == 0 {
                    return v_bs_6235_;
                } else {
                    v_v_6237_ = lean_array_uget(v_bs_6235_, v_i_6234_);
                    v___x_6238_ = lean_unsigned_to_nat(0);
                    v_bs_x27_6239_ = lean_array_uset(v_bs_6235_, v_i_6234_, v___x_6238_);
                    v___x_6240_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_6237_);
                    lean_dec(v_v_6237_);
                    v___x_6241_ = 1usize;
                    v___x_6242_ = lean_usize_add(v_i_6234_, v___x_6241_);
                    v___x_6243_ = lean_array_uset(v_bs_x27_6239_, v_i_6234_, v___x_6240_);
                    v_i_6234_ = v___x_6242_;
                    v_bs_6235_ = v___x_6243_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2___boxed(
    mut v_sz_6245_: *mut LeanObject,
    mut v_i_6246_: *mut LeanObject,
    mut v_bs_6247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6248_: usize = 0;
    let mut v_i_boxed_6249_: usize = 0;
    let mut v_res_6250_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6248_ = lean_unbox_usize(v_sz_6245_);
    lean_dec(v_sz_6245_);
    v_i_boxed_6249_ = lean_unbox_usize(v_i_6246_);
    lean_dec(v_i_6246_);
    v_res_6250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_boxed_6248_, v_i_boxed_6249_, v_bs_6247_);
    return v_res_6250_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExtractLets(
    mut v_x_6271_: *mut LeanObject,
    mut v_a_6272_: *mut LeanObject,
    mut v_a_6273_: *mut LeanObject,
    mut v_a_6274_: *mut LeanObject,
    mut v_a_6275_: *mut LeanObject,
    mut v_a_6276_: *mut LeanObject,
    mut v_a_6277_: *mut LeanObject,
    mut v_a_6278_: *mut LeanObject,
    mut v_a_6279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: u8 = 0;
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: u8 = 0;
    let mut v___x_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_loc_x3f_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: u8 = 0;
    let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6323_: usize = 0;
    let mut v___x_6324_: usize = 0;
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6334_: u8 = 0;
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6338_: u8 = 0;
    let mut v_a_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6342_: u8 = 0;
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6346_: u8 = 0;
    let mut v___x_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: u8 = 0;
    let mut v___x_6350_: u8 = 0;
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_loc_x3f_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: u8 = 0;
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6297_ = l_Lean_Elab_Tactic_evalExtractLets___closed__2;
                lean_inc(v_x_6271_);
                v___x_6298_ = l_Lean_Syntax_isOfKind(v_x_6271_, v___x_6297_);
                if v___x_6298_ == 0 {
                    lean_dec(v_x_6271_);
                    v___x_6299_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
                    return v___x_6299_;
                } else {
                    v___x_6300_ = lean_unsigned_to_nat(1);
                    v___x_6301_ = l_Lean_Syntax_getArg(v_x_6271_, v___x_6300_);
                    v___x_6302_ = l_Lean_Elab_Tactic_evalExtractLets___closed__4;
                    lean_inc(v___x_6301_);
                    v___x_6303_ = l_Lean_Syntax_isOfKind(v___x_6301_, v___x_6302_);
                    if v___x_6303_ == 0 {
                        lean_dec(v___x_6301_);
                        lean_dec(v_x_6271_);
                        v___x_6304_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
                        return v___x_6304_;
                    } else {
                        v___f_6305_ = l_Lean_Elab_Tactic_evalExtractLets___closed__5;
                        v___x_6306_ = lean_unsigned_to_nat(2);
                        v___x_6307_ = l_Lean_Syntax_getArg(v_x_6271_, v___x_6306_);
                        v___x_6347_ = lean_unsigned_to_nat(3);
                        v___x_6348_ = l_Lean_Syntax_getArg(v_x_6271_, v___x_6347_);
                        lean_dec(v_x_6271_);
                        v___x_6349_ = l_Lean_Syntax_isNone(v___x_6348_);
                        if v___x_6349_ == 0 {
                            lean_inc(v___x_6348_);
                            v___x_6350_ = l_Lean_Syntax_matchesNull(v___x_6348_, v___x_6300_);
                            if v___x_6350_ == 0 {
                                lean_dec(v___x_6348_);
                                lean_dec(v___x_6307_);
                                lean_dec(v___x_6301_);
                                v___x_6351_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
                                return v___x_6351_;
                            } else {
                                v___x_6352_ = lean_unsigned_to_nat(0);
                                v_loc_x3f_6353_ = l_Lean_Syntax_getArg(v___x_6348_, v___x_6352_);
                                lean_dec(v___x_6348_);
                                v___x_6354_ = l_Lean_Elab_Tactic_evalExtractLets___closed__7;
                                lean_inc(v_loc_x3f_6353_);
                                v___x_6355_ = l_Lean_Syntax_isOfKind(v_loc_x3f_6353_, v___x_6354_);
                                if v___x_6355_ == 0 {
                                    lean_dec(v_loc_x3f_6353_);
                                    lean_dec(v___x_6307_);
                                    lean_dec(v___x_6301_);
                                    v___x_6356_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
                                    return v___x_6356_;
                                } else {
                                    v___x_6357_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_6357_, 0, v_loc_x3f_6353_);
                                    v_loc_x3f_6309_ = v___x_6357_;
                                    v___y_6310_ = v_a_6272_;
                                    v___y_6311_ = v_a_6273_;
                                    v___y_6312_ = v_a_6274_;
                                    v___y_6313_ = v_a_6275_;
                                    v___y_6314_ = v_a_6276_;
                                    v___y_6315_ = v_a_6277_;
                                    v___y_6316_ = v_a_6278_;
                                    v___y_6317_ = v_a_6279_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_6348_);
                            v___x_6358_ = lean_box(0);
                            v_loc_x3f_6309_ = v___x_6358_;
                            v___y_6310_ = v_a_6272_;
                            v___y_6311_ = v_a_6273_;
                            v___y_6312_ = v_a_6274_;
                            v___y_6313_ = v_a_6275_;
                            v___y_6314_ = v_a_6276_;
                            v___y_6315_ = v_a_6277_;
                            v___y_6316_ = v_a_6278_;
                            v___y_6317_ = v_a_6279_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6294_ = l_Lean_mkOptionalNode(v___y_6293_);
                v___x_6295_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_6294_);
                lean_dec(v___x_6294_);
                lean_inc_ref(v___y_6285_);
                v___x_6296_ = l_Lean_Elab_Tactic_withLocation(
                    v___x_6295_,
                    v___y_6291_,
                    v___y_6289_,
                    v___y_6285_,
                    v___y_6288_,
                    v___y_6284_,
                    v___y_6292_,
                    v___y_6286_,
                    v___y_6290_,
                    v___y_6287_,
                    v___y_6282_,
                    v___y_6283_,
                );
                lean_dec(v___x_6295_);
                return v___x_6296_;
            }
            2 => {
                v___x_6318_ = 0;
                v___x_6319_ = lean_alloc_ctor(0, 0, (11) as u32);
                lean_ctor_set_uint8(v___x_6319_, 0 as u32, v___x_6318_);
                lean_ctor_set_uint8(v___x_6319_, 1 as u32, v___x_6303_);
                lean_ctor_set_uint8(v___x_6319_, 2 as u32, v___x_6318_);
                lean_ctor_set_uint8(v___x_6319_, 3 as u32, v___x_6303_);
                lean_ctor_set_uint8(v___x_6319_, 4 as u32, v___x_6303_);
                lean_ctor_set_uint8(v___x_6319_, 5 as u32, v___x_6318_);
                lean_ctor_set_uint8(v___x_6319_, 6 as u32, v___x_6303_);
                lean_ctor_set_uint8(v___x_6319_, 7 as u32, v___x_6303_);
                lean_ctor_set_uint8(v___x_6319_, 8 as u32, v___x_6318_);
                lean_ctor_set_uint8(v___x_6319_, 9 as u32, v___x_6318_);
                lean_ctor_set_uint8(v___x_6319_, 10 as u32, v___x_6318_);
                v___x_6320_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(
                    v___x_6301_,
                    v___x_6319_,
                    v___x_6303_,
                    v___y_6310_,
                    v___y_6316_,
                    v___y_6317_,
                );
                if lean_obj_tag(v___x_6320_) == 0 {
                    v_a_6321_ = lean_ctor_get(v___x_6320_, 0);
                    lean_inc_n(v_a_6321_, 2);
                    lean_dec_ref_known(v___x_6320_, 1);
                    v_ids_6322_ = l_Lean_Syntax_getArgs(v___x_6307_);
                    lean_dec(v___x_6307_);
                    v_sz_6323_ = lean_array_size(v_ids_6322_);
                    v___x_6324_ = 0usize;
                    lean_inc_ref_n(v_ids_6322_, 2);
                    v___x_6325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_6323_, v___x_6324_, v_ids_6322_);
                    v___x_6326_ = lean_array_to_list(v___x_6325_);
                    lean_inc(v___x_6326_);
                    v___f_6327_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed
                            as *mut core::ffi::c_void,
                        13,
                        3,
                    );
                    lean_closure_set(v___f_6327_, 0, v___x_6326_);
                    lean_closure_set(v___f_6327_, 1, v_a_6321_);
                    lean_closure_set(v___f_6327_, 2, v_ids_6322_);
                    v___f_6328_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed
                            as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    lean_closure_set(v___f_6328_, 0, v___x_6326_);
                    lean_closure_set(v___f_6328_, 1, v_a_6321_);
                    v___f_6329_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed
                            as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    lean_closure_set(v___f_6329_, 0, v___f_6328_);
                    lean_closure_set(v___f_6329_, 1, v_ids_6322_);
                    if lean_obj_tag(v_loc_x3f_6309_) == 0 {
                        v___x_6330_ = lean_box(0);
                        v___y_6282_ = v___y_6316_;
                        v___y_6283_ = v___y_6317_;
                        v___y_6284_ = v___y_6311_;
                        v___y_6285_ = v___f_6305_;
                        v___y_6286_ = v___y_6313_;
                        v___y_6287_ = v___y_6315_;
                        v___y_6288_ = v___y_6310_;
                        v___y_6289_ = v___f_6329_;
                        v___y_6290_ = v___y_6314_;
                        v___y_6291_ = v___f_6327_;
                        v___y_6292_ = v___y_6312_;
                        v___y_6293_ = v___x_6330_;
                        state = 1;
                        continue;
                    } else {
                        v_val_6331_ = lean_ctor_get(v_loc_x3f_6309_, 0);
                        v_isSharedCheck_6338_ = (!lean_is_exclusive(v_loc_x3f_6309_)) as u8;
                        if v_isSharedCheck_6338_ == 0 {
                            v___x_6333_ = v_loc_x3f_6309_;
                            v_isShared_6334_ = v_isSharedCheck_6338_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_6331_);
                            lean_dec(v_loc_x3f_6309_);
                            v___x_6333_ = lean_box(0);
                            v_isShared_6334_ = v_isSharedCheck_6338_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_loc_x3f_6309_);
                    lean_dec(v___x_6307_);
                    v_a_6339_ = lean_ctor_get(v___x_6320_, 0);
                    v_isSharedCheck_6346_ = (!lean_is_exclusive(v___x_6320_)) as u8;
                    if v_isSharedCheck_6346_ == 0 {
                        v___x_6341_ = v___x_6320_;
                        v_isShared_6342_ = v_isSharedCheck_6346_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6339_);
                        lean_dec(v___x_6320_);
                        v___x_6341_ = lean_box(0);
                        v_isShared_6342_ = v_isSharedCheck_6346_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6334_ == 0 {
                    v___x_6336_ = v___x_6333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6337_, 0, v_val_6331_);
                    v___x_6336_ = v_reuseFailAlloc_6337_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_6282_ = v___y_6316_;
                v___y_6283_ = v___y_6317_;
                v___y_6284_ = v___y_6311_;
                v___y_6285_ = v___f_6305_;
                v___y_6286_ = v___y_6313_;
                v___y_6287_ = v___y_6315_;
                v___y_6288_ = v___y_6310_;
                v___y_6289_ = v___f_6329_;
                v___y_6290_ = v___y_6314_;
                v___y_6291_ = v___f_6327_;
                v___y_6292_ = v___y_6312_;
                v___y_6293_ = v___x_6336_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_6342_ == 0 {
                    v___x_6344_ = v___x_6341_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6345_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6345_, 0, v_a_6339_);
                    v___x_6344_ = v_reuseFailAlloc_6345_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalExtractLets___boxed(
    mut v_x_6359_: *mut LeanObject,
    mut v_a_6360_: *mut LeanObject,
    mut v_a_6361_: *mut LeanObject,
    mut v_a_6362_: *mut LeanObject,
    mut v_a_6363_: *mut LeanObject,
    mut v_a_6364_: *mut LeanObject,
    mut v_a_6365_: *mut LeanObject,
    mut v_a_6366_: *mut LeanObject,
    mut v_a_6367_: *mut LeanObject,
    mut v_a_6368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6369_: *mut LeanObject = core::ptr::null_mut();
    v_res_6369_ = l_Lean_Elab_Tactic_evalExtractLets(
        v_x_6359_, v_a_6360_, v_a_6361_, v_a_6362_, v_a_6363_, v_a_6364_, v_a_6365_, v_a_6366_,
        v_a_6367_,
    );
    lean_dec(v_a_6367_);
    lean_dec_ref(v_a_6366_);
    lean_dec(v_a_6365_);
    lean_dec_ref(v_a_6364_);
    lean_dec(v_a_6363_);
    lean_dec_ref(v_a_6362_);
    lean_dec(v_a_6361_);
    lean_dec_ref(v_a_6360_);
    return v_res_6369_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(
    mut v_00_u03b1_6370_: *mut LeanObject,
    mut v_msg_6371_: *mut LeanObject,
    mut v___y_6372_: *mut LeanObject,
    mut v___y_6373_: *mut LeanObject,
    mut v___y_6374_: *mut LeanObject,
    mut v___y_6375_: *mut LeanObject,
    mut v___y_6376_: *mut LeanObject,
    mut v___y_6377_: *mut LeanObject,
    mut v___y_6378_: *mut LeanObject,
    mut v___y_6379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    v___x_6381_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(
        v_msg_6371_,
        v___y_6376_,
        v___y_6377_,
        v___y_6378_,
        v___y_6379_,
    );
    return v___x_6381_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___boxed(
    mut v_00_u03b1_6382_: *mut LeanObject,
    mut v_msg_6383_: *mut LeanObject,
    mut v___y_6384_: *mut LeanObject,
    mut v___y_6385_: *mut LeanObject,
    mut v___y_6386_: *mut LeanObject,
    mut v___y_6387_: *mut LeanObject,
    mut v___y_6388_: *mut LeanObject,
    mut v___y_6389_: *mut LeanObject,
    mut v___y_6390_: *mut LeanObject,
    mut v___y_6391_: *mut LeanObject,
    mut v___y_6392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6393_: *mut LeanObject = core::ptr::null_mut();
    v_res_6393_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(
        v_00_u03b1_6382_,
        v_msg_6383_,
        v___y_6384_,
        v___y_6385_,
        v___y_6386_,
        v___y_6387_,
        v___y_6388_,
        v___y_6389_,
        v___y_6390_,
        v___y_6391_,
    );
    lean_dec(v___y_6391_);
    lean_dec_ref(v___y_6390_);
    lean_dec(v___y_6389_);
    lean_dec_ref(v___y_6388_);
    lean_dec(v___y_6387_);
    lean_dec_ref(v___y_6386_);
    lean_dec(v___y_6385_);
    lean_dec_ref(v___y_6384_);
    return v_res_6393_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1()
-> *mut LeanObject {
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    v___x_6401_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_6402_ = l_Lean_Elab_Tactic_evalExtractLets___closed__2;
    v___x_6403_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1;
    v___x_6404_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalExtractLets___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_6405_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6401_,
        v___x_6402_,
        v___x_6403_,
        v___x_6404_,
    );
    return v___x_6405_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___boxed(
    mut v_a_6406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6407_: *mut LeanObject = core::ptr::null_mut();
    v_res_6407_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
    return v_res_6407_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0(
    mut v_ctor_6408_: *mut LeanObject,
    mut v_args_6409_: *mut LeanObject,
    mut v___y_6410_: *mut LeanObject,
    mut v___y_6411_: *mut LeanObject,
    mut v___y_6412_: *mut LeanObject,
    mut v___y_6413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6423_: u8 = 0;
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6427_: u8 = 0;
    let mut v_a_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6431_: u8 = 0;
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6435_: u8 = 0;
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: u8 = 0;
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: u8 = 0;
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6447_: u8 = 0;
    let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6436_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__0;
                v___x_6437_ = lean_string_dec_eq(v_ctor_6408_, v___x_6436_);
                if v___x_6437_ == 0 {
                    v___x_6438_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__0___redArg();
                    return v___x_6438_;
                } else {
                    v___x_6439_ = lean_array_get_size(v_args_6409_);
                    v___x_6440_ = lean_unsigned_to_nat(1);
                    v___x_6441_ = lean_nat_dec_eq(v___x_6439_, v___x_6440_);
                    if v___x_6441_ == 0 {
                        v___x_6442_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr___lam__0___closed__2);
                        v___x_6443_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr_spec__1___redArg(v___x_6442_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_);
                        v_a_6444_ = lean_ctor_get(v___x_6443_, 0);
                        v_isSharedCheck_6451_ = (!lean_is_exclusive(v___x_6443_)) as u8;
                        if v_isSharedCheck_6451_ == 0 {
                            v___x_6446_ = v___x_6443_;
                            v_isShared_6447_ = v_isSharedCheck_6451_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6444_);
                            lean_dec(v___x_6443_);
                            v___x_6446_ = lean_box(0);
                            v_isShared_6447_ = v_isSharedCheck_6451_;
                            state = 6;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6416_ = l_Lean_instInhabitedExpr;
                v___x_6417_ = lean_unsigned_to_nat(0);
                v___x_6418_ = lean_array_get_borrowed(v___x_6416_, v_args_6409_, v___x_6417_);
                lean_inc(v___x_6418_);
                v___x_6419_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig_evalExpr(v___x_6418_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_);
                if lean_obj_tag(v___x_6419_) == 0 {
                    v_a_6420_ = lean_ctor_get(v___x_6419_, 0);
                    v_isSharedCheck_6427_ = (!lean_is_exclusive(v___x_6419_)) as u8;
                    if v_isSharedCheck_6427_ == 0 {
                        v___x_6422_ = v___x_6419_;
                        v_isShared_6423_ = v_isSharedCheck_6427_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6420_);
                        lean_dec(v___x_6419_);
                        v___x_6422_ = lean_box(0);
                        v_isShared_6423_ = v_isSharedCheck_6427_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6428_ = lean_ctor_get(v___x_6419_, 0);
                    v_isSharedCheck_6435_ = (!lean_is_exclusive(v___x_6419_)) as u8;
                    if v_isSharedCheck_6435_ == 0 {
                        v___x_6430_ = v___x_6419_;
                        v_isShared_6431_ = v_isSharedCheck_6435_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6428_);
                        lean_dec(v___x_6419_);
                        v___x_6430_ = lean_box(0);
                        v_isShared_6431_ = v_isSharedCheck_6435_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6423_ == 0 {
                    v___x_6425_ = v___x_6422_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6426_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6426_, 0, v_a_6420_);
                    v___x_6425_ = v_reuseFailAlloc_6426_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6425_;
            }
            4 => {
                if v_isShared_6431_ == 0 {
                    v___x_6433_ = v___x_6430_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6434_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6434_, 0, v_a_6428_);
                    v___x_6433_ = v_reuseFailAlloc_6434_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6433_;
            }
            6 => {
                if v_isShared_6447_ == 0 {
                    v___x_6449_ = v___x_6446_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6450_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6450_, 0, v_a_6444_);
                    v___x_6449_ = v_reuseFailAlloc_6450_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6449_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0___boxed(
    mut v_ctor_6452_: *mut LeanObject,
    mut v_args_6453_: *mut LeanObject,
    mut v___y_6454_: *mut LeanObject,
    mut v___y_6455_: *mut LeanObject,
    mut v___y_6456_: *mut LeanObject,
    mut v___y_6457_: *mut LeanObject,
    mut v___y_6458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6459_: *mut LeanObject = core::ptr::null_mut();
    v_res_6459_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___lam__0(v_ctor_6452_, v_args_6453_, v___y_6454_, v___y_6455_, v___y_6456_, v___y_6457_);
    lean_dec(v___y_6457_);
    lean_dec_ref(v___y_6456_);
    lean_dec(v___y_6455_);
    lean_dec_ref(v___y_6454_);
    lean_dec_ref(v_args_6453_);
    lean_dec_ref(v_ctor_6452_);
    return v_res_6459_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(
    mut v_a_6466_: *mut LeanObject,
    mut v_a_6467_: *mut LeanObject,
    mut v_a_6468_: *mut LeanObject,
    mut v_a_6469_: *mut LeanObject,
    mut v_a_6470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    v___f_6472_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__0;
    v___x_6473_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2;
    v___x_6474_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
        v___x_6473_,
        v___f_6472_,
        v_a_6466_,
        v_a_6467_,
        v_a_6468_,
        v_a_6469_,
        v_a_6470_,
    );
    return v___x_6474_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___boxed(
    mut v_a_6475_: *mut LeanObject,
    mut v_a_6476_: *mut LeanObject,
    mut v_a_6477_: *mut LeanObject,
    mut v_a_6478_: *mut LeanObject,
    mut v_a_6479_: *mut LeanObject,
    mut v_a_6480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6481_: *mut LeanObject = core::ptr::null_mut();
    v_res_6481_ =
        l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(
            v_a_6475_, v_a_6476_, v_a_6477_, v_a_6478_, v_a_6479_,
        );
    lean_dec(v_a_6479_);
    lean_dec_ref(v_a_6478_);
    lean_dec(v_a_6477_);
    lean_dec_ref(v_a_6476_);
    return v_res_6481_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1()
-> *mut LeanObject {
    let mut v___x_6483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut LeanObject = core::ptr::null_mut();
    v___x_6483_ = lean_box(0);
    v___x_6484_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2;
    v___x_6485_ = l_Lean_Expr_const___override(v___x_6484_, v___x_6483_);
    return v___x_6485_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2()
-> *mut LeanObject {
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: *mut LeanObject = core::ptr::null_mut();
    v___x_6486_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1);
    v___x_6487_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6487_, 0, v___x_6486_);
    return v___x_6487_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3()
-> *mut LeanObject {
    let mut v___x_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
    v___x_6488_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2);
    v___x_6489_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__0;
    v___x_6490_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6490_, 0, v___x_6489_);
    lean_ctor_set(v___x_6490_, 1, v___x_6488_);
    return v___x_6490_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig()
-> *mut LeanObject {
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    v___x_6491_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3_once), _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__3);
    return v___x_6491_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    v___x_6492_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__1);
    v___x_6493_ = l_Lean_MessageData_ofExpr(v___x_6492_);
    return v___x_6493_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    v___x_6494_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__0);
    v___x_6495_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__1);
    v___x_6496_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_6496_, 0, v___x_6495_);
    lean_ctor_set(v___x_6496_, 1, v___x_6494_);
    return v___x_6496_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    v___x_6497_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__5);
    v___x_6498_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__1);
    v___x_6499_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_6499_, 0, v___x_6498_);
    lean_ctor_set(v___x_6499_, 1, v___x_6497_);
    return v___x_6499_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(
    mut v_stx_6500_: *mut LeanObject,
    mut v_a_6501_: *mut LeanObject,
    mut v_a_6502_: *mut LeanObject,
    mut v_a_6503_: *mut LeanObject,
    mut v_a_6504_: *mut LeanObject,
    mut v_a_6505_: *mut LeanObject,
    mut v_a_6506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ty_x3f_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: u8 = 0;
    let mut v___x_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6526_: u8 = 0;
    let mut v_cancelTk_x3f_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6528_: u8 = 0;
    let mut v_inheritedTraceOptions_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: u8 = 0;
    let mut v_ref_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6547_: u8 = 0;
    let mut v_id_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6551_: u8 = 0;
    let mut v___x_6552_: u8 = 0;
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6561_: u8 = 0;
    let mut v_unused_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: u8 = 0;
    let mut v___x_6574_: u8 = 0;
    let mut v___y_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: u8 = 0;
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6591_: u8 = 0;
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6595_: u8 = 0;
    let mut v_a_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6599_: u8 = 0;
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6603_: u8 = 0;
    let mut v_a_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6607_: u8 = 0;
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6611_: u8 = 0;
    let mut v___y_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6626_: u8 = 0;
    let mut v___x_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6630_: u8 = 0;
    let mut v___x_6631_: u8 = 0;
    let mut v___x_6632_: u8 = 0;
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6637_: u8 = 0;
    let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6641_: u8 = 0;
    let mut v_a_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6645_: u8 = 0;
    let mut v___x_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ty_x3f_6508_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig___closed__2);
                v___x_6509_ = 1;
                v___x_6510_ = lean_box(0);
                v___x_6511_ = lean_box((v___x_6509_) as usize);
                v___x_6512_ = lean_box((v___x_6509_) as usize);
                lean_inc(v_stx_6500_);
                v___x_6513_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___x_6513_, 0, v_stx_6500_);
                lean_closure_set(v___x_6513_, 1, v_ty_x3f_6508_);
                lean_closure_set(v___x_6513_, 2, v___x_6511_);
                lean_closure_set(v___x_6513_, 3, v___x_6512_);
                lean_closure_set(v___x_6513_, 4, v___x_6510_);
                v_fileName_6514_ = lean_ctor_get(v_a_6505_, 0);
                v_fileMap_6515_ = lean_ctor_get(v_a_6505_, 1);
                v_options_6516_ = lean_ctor_get(v_a_6505_, 2);
                v_currRecDepth_6517_ = lean_ctor_get(v_a_6505_, 3);
                v_maxRecDepth_6518_ = lean_ctor_get(v_a_6505_, 4);
                v_ref_6519_ = lean_ctor_get(v_a_6505_, 5);
                v_currNamespace_6520_ = lean_ctor_get(v_a_6505_, 6);
                v_openDecls_6521_ = lean_ctor_get(v_a_6505_, 7);
                v_initHeartbeats_6522_ = lean_ctor_get(v_a_6505_, 8);
                v_maxHeartbeats_6523_ = lean_ctor_get(v_a_6505_, 9);
                v_quotContext_6524_ = lean_ctor_get(v_a_6505_, 10);
                v_currMacroScope_6525_ = lean_ctor_get(v_a_6505_, 11);
                v_diag_6526_ = lean_ctor_get_uint8(
                    v_a_6505_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6527_ = lean_ctor_get(v_a_6505_, 12);
                v_suppressElabErrors_6528_ = lean_ctor_get_uint8(
                    v_a_6505_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6529_ = lean_ctor_get(v_a_6505_, 13);
                v___x_6530_ = 1;
                v_ref_6531_ = l_Lean_replaceRef(v_stx_6500_, v_ref_6519_);
                lean_dec(v_stx_6500_);
                lean_inc_ref(v_inheritedTraceOptions_6529_);
                lean_inc(v_cancelTk_x3f_6527_);
                lean_inc(v_currMacroScope_6525_);
                lean_inc(v_quotContext_6524_);
                lean_inc(v_maxHeartbeats_6523_);
                lean_inc(v_initHeartbeats_6522_);
                lean_inc(v_openDecls_6521_);
                lean_inc(v_currNamespace_6520_);
                lean_inc(v_maxRecDepth_6518_);
                lean_inc(v_currRecDepth_6517_);
                lean_inc_ref(v_options_6516_);
                lean_inc_ref(v_fileMap_6515_);
                lean_inc_ref(v_fileName_6514_);
                v___x_6532_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_6532_, 0, v_fileName_6514_);
                lean_ctor_set(v___x_6532_, 1, v_fileMap_6515_);
                lean_ctor_set(v___x_6532_, 2, v_options_6516_);
                lean_ctor_set(v___x_6532_, 3, v_currRecDepth_6517_);
                lean_ctor_set(v___x_6532_, 4, v_maxRecDepth_6518_);
                lean_ctor_set(v___x_6532_, 5, v_ref_6531_);
                lean_ctor_set(v___x_6532_, 6, v_currNamespace_6520_);
                lean_ctor_set(v___x_6532_, 7, v_openDecls_6521_);
                lean_ctor_set(v___x_6532_, 8, v_initHeartbeats_6522_);
                lean_ctor_set(v___x_6532_, 9, v_maxHeartbeats_6523_);
                lean_ctor_set(v___x_6532_, 10, v_quotContext_6524_);
                lean_ctor_set(v___x_6532_, 11, v_currMacroScope_6525_);
                lean_ctor_set(v___x_6532_, 12, v_cancelTk_x3f_6527_);
                lean_ctor_set(v___x_6532_, 13, v_inheritedTraceOptions_6529_);
                lean_ctor_set_uint8(
                    v___x_6532_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_6526_,
                );
                lean_ctor_set_uint8(
                    v___x_6532_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_6528_,
                );
                v___x_6533_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_6513_,
                        v___x_6530_,
                        v_a_6501_,
                        v_a_6502_,
                        v_a_6503_,
                        v_a_6504_,
                        v___x_6532_,
                        v_a_6506_,
                    );
                if lean_obj_tag(v___x_6533_) == 0 {
                    v_a_6534_ = lean_ctor_get(v___x_6533_, 0);
                    lean_inc(v_a_6534_);
                    lean_dec_ref_known(v___x_6533_, 1);
                    v___x_6535_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_6534_, v_a_6504_);
                    v_a_6536_ = lean_ctor_get(v___x_6535_, 0);
                    lean_inc(v_a_6536_);
                    lean_dec_ref(v___x_6535_);
                    v___x_6631_ = l_Lean_Expr_hasSorry(v_a_6536_);
                    if v___x_6631_ == 0 {
                        v___y_6576_ = v_a_6501_;
                        v___y_6577_ = v_a_6502_;
                        v___y_6578_ = v_a_6503_;
                        v___y_6579_ = v_a_6504_;
                        v___y_6580_ = v___x_6532_;
                        v___y_6581_ = v_a_6506_;
                        state = 5;
                        continue;
                    } else {
                        v___x_6632_ = l_Lean_Expr_hasSyntheticSorry(v_a_6536_);
                        if v___x_6632_ == 0 {
                            v___y_6613_ = v_a_6501_;
                            v___y_6614_ = v_a_6502_;
                            v___y_6615_ = v_a_6503_;
                            v___y_6616_ = v_a_6504_;
                            v___y_6617_ = v___x_6532_;
                            v___y_6618_ = v_a_6506_;
                            state = 12;
                            continue;
                        } else {
                            lean_dec(v_a_6536_);
                            lean_dec_ref_known(v___x_6532_, 14);
                            v___x_6633_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
                            v_a_6634_ = lean_ctor_get(v___x_6633_, 0);
                            v_isSharedCheck_6641_ = (!lean_is_exclusive(v___x_6633_)) as u8;
                            if v_isSharedCheck_6641_ == 0 {
                                v___x_6636_ = v___x_6633_;
                                v_isShared_6637_ = v_isSharedCheck_6641_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_6634_);
                                lean_dec(v___x_6633_);
                                v___x_6636_ = lean_box(0);
                                v_isShared_6637_ = v_isSharedCheck_6641_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_6532_, 14);
                    v_a_6642_ = lean_ctor_get(v___x_6533_, 0);
                    v_isSharedCheck_6649_ = (!lean_is_exclusive(v___x_6533_)) as u8;
                    if v_isSharedCheck_6649_ == 0 {
                        v___x_6644_ = v___x_6533_;
                        v_isShared_6645_ = v_isSharedCheck_6649_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_6642_);
                        lean_dec(v___x_6533_);
                        v___x_6644_ = lean_box(0);
                        v_isShared_6645_ = v_isSharedCheck_6649_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6547_ == 0 {
                    if lean_obj_tag(v___y_6540_) == 0 {
                        lean_dec_ref_known(v___y_6540_, 2);
                        lean_dec_ref(v___y_6543_);
                        lean_dec(v_a_6536_);
                        return v___y_6539_;
                    } else {
                        v_id_6548_ = lean_ctor_get(v___y_6540_, 0);
                        v_isSharedCheck_6561_ = (!lean_is_exclusive(v___y_6540_)) as u8;
                        if v_isSharedCheck_6561_ == 0 {
                            v_unused_6562_ = lean_ctor_get(v___y_6540_, 1);
                            lean_dec(v_unused_6562_);
                            v___x_6550_ = v___y_6540_;
                            v_isShared_6551_ = v_isSharedCheck_6561_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_id_6548_);
                            lean_dec(v___y_6540_);
                            v___x_6550_ = lean_box(0);
                            v_isShared_6551_ = v_isSharedCheck_6561_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6543_);
                    lean_dec_ref(v___y_6540_);
                    lean_dec(v_a_6536_);
                    return v___y_6539_;
                }
            }
            2 => {
                v___x_6552_ = l_Lean_instBEqInternalExceptionId_beq(v___y_6545_, v_id_6548_);
                lean_dec(v_id_6548_);
                if v___x_6552_ == 0 {
                    lean_del_object(v___x_6550_);
                    lean_dec_ref(v___y_6543_);
                    lean_dec(v_a_6536_);
                    return v___y_6539_;
                } else {
                    lean_dec_ref(v___y_6539_);
                    v___x_6553_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___closed__2);
                    v___x_6554_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__8);
                    v___x_6555_ = l_Lean_indentExpr(v_a_6536_);
                    if v_isShared_6551_ == 0 {
                        lean_ctor_set_tag(v___x_6550_, 7);
                        lean_ctor_set(v___x_6550_, 1, v___x_6555_);
                        lean_ctor_set(v___x_6550_, 0, v___x_6554_);
                        v___x_6557_ = v___x_6550_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6560_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6560_, 0, v___x_6554_);
                        lean_ctor_set(v_reuseFailAlloc_6560_, 1, v___x_6555_);
                        v___x_6557_ = v_reuseFailAlloc_6560_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6558_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6558_, 0, v___x_6557_);
                lean_ctor_set(v___x_6558_, 1, v___x_6553_);
                v___x_6559_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_6558_, v___y_6546_, v___y_6541_, v___y_6538_, v___y_6544_, v___y_6543_, v___y_6542_);
                lean_dec_ref(v___y_6543_);
                return v___x_6559_;
            }
            4 => {
                lean_inc(v_a_6536_);
                v___x_6570_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr(v_a_6536_, v___y_6566_, v___y_6567_, v___y_6568_, v___y_6569_);
                if lean_obj_tag(v___x_6570_) == 0 {
                    lean_dec_ref(v___y_6568_);
                    lean_dec(v_a_6536_);
                    return v___x_6570_;
                } else {
                    v_a_6571_ = lean_ctor_get(v___x_6570_, 0);
                    lean_inc(v_a_6571_);
                    v___x_6572_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_6573_ = l_Lean_Exception_isInterrupt(v_a_6571_);
                    if v___x_6573_ == 0 {
                        lean_inc(v_a_6571_);
                        v___x_6574_ = l_Lean_Exception_isRuntime(v_a_6571_);
                        v___y_6538_ = v___y_6566_;
                        v___y_6539_ = v___x_6570_;
                        v___y_6540_ = v_a_6571_;
                        v___y_6541_ = v___y_6565_;
                        v___y_6542_ = v___y_6569_;
                        v___y_6543_ = v___y_6568_;
                        v___y_6544_ = v___y_6567_;
                        v___y_6545_ = v___x_6572_;
                        v___y_6546_ = v___y_6564_;
                        v___y_6547_ = v___x_6574_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6538_ = v___y_6566_;
                        v___y_6539_ = v___x_6570_;
                        v___y_6540_ = v_a_6571_;
                        v___y_6541_ = v___y_6565_;
                        v___y_6542_ = v___y_6569_;
                        v___y_6543_ = v___y_6568_;
                        v___y_6544_ = v___y_6567_;
                        v___y_6545_ = v___x_6572_;
                        v___y_6546_ = v___y_6564_;
                        v___y_6547_ = v___x_6573_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_6536_);
                v___x_6582_ = l_Lean_Meta_getMVars(
                    v_a_6536_,
                    v___y_6578_,
                    v___y_6579_,
                    v___y_6580_,
                    v___y_6581_,
                );
                if lean_obj_tag(v___x_6582_) == 0 {
                    v_a_6583_ = lean_ctor_get(v___x_6582_, 0);
                    lean_inc(v_a_6583_);
                    lean_dec_ref_known(v___x_6582_, 1);
                    v___x_6584_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                        v_a_6583_,
                        v___x_6510_,
                        v___y_6576_,
                        v___y_6577_,
                        v___y_6578_,
                        v___y_6579_,
                        v___y_6580_,
                        v___y_6581_,
                    );
                    lean_dec(v_a_6583_);
                    if lean_obj_tag(v___x_6584_) == 0 {
                        v_a_6585_ = lean_ctor_get(v___x_6584_, 0);
                        lean_inc(v_a_6585_);
                        lean_dec_ref_known(v___x_6584_, 1);
                        v___x_6586_ = (lean_unbox(v_a_6585_) as u8);
                        lean_dec(v_a_6585_);
                        if v___x_6586_ == 0 {
                            v___y_6564_ = v___y_6576_;
                            v___y_6565_ = v___y_6577_;
                            v___y_6566_ = v___y_6578_;
                            v___y_6567_ = v___y_6579_;
                            v___y_6568_ = v___y_6580_;
                            v___y_6569_ = v___y_6581_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v___y_6580_);
                            lean_dec(v_a_6536_);
                            v___x_6587_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__2___redArg();
                            v_a_6588_ = lean_ctor_get(v___x_6587_, 0);
                            v_isSharedCheck_6595_ = (!lean_is_exclusive(v___x_6587_)) as u8;
                            if v_isSharedCheck_6595_ == 0 {
                                v___x_6590_ = v___x_6587_;
                                v_isShared_6591_ = v_isSharedCheck_6595_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_6588_);
                                lean_dec(v___x_6587_);
                                v___x_6590_ = lean_box(0);
                                v_isShared_6591_ = v_isSharedCheck_6595_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_6580_);
                        lean_dec(v_a_6536_);
                        v_a_6596_ = lean_ctor_get(v___x_6584_, 0);
                        v_isSharedCheck_6603_ = (!lean_is_exclusive(v___x_6584_)) as u8;
                        if v_isSharedCheck_6603_ == 0 {
                            v___x_6598_ = v___x_6584_;
                            v_isShared_6599_ = v_isSharedCheck_6603_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_6596_);
                            lean_dec(v___x_6584_);
                            v___x_6598_ = lean_box(0);
                            v_isShared_6599_ = v_isSharedCheck_6603_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6580_);
                    lean_dec(v_a_6536_);
                    v_a_6604_ = lean_ctor_get(v___x_6582_, 0);
                    v_isSharedCheck_6611_ = (!lean_is_exclusive(v___x_6582_)) as u8;
                    if v_isSharedCheck_6611_ == 0 {
                        v___x_6606_ = v___x_6582_;
                        v_isShared_6607_ = v_isSharedCheck_6611_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6604_);
                        lean_dec(v___x_6582_);
                        v___x_6606_ = lean_box(0);
                        v_isShared_6607_ = v_isSharedCheck_6611_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_6591_ == 0 {
                    v___x_6593_ = v___x_6590_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6594_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 0, v_a_6588_);
                    v___x_6593_ = v_reuseFailAlloc_6594_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6593_;
            }
            8 => {
                if v_isShared_6599_ == 0 {
                    v___x_6601_ = v___x_6598_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6602_, 0, v_a_6596_);
                    v___x_6601_ = v_reuseFailAlloc_6602_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6601_;
            }
            10 => {
                if v_isShared_6607_ == 0 {
                    v___x_6609_ = v___x_6606_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6610_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6610_, 0, v_a_6604_);
                    v___x_6609_ = v_reuseFailAlloc_6610_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6609_;
            }
            12 => {
                v___x_6619_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0___closed__10);
                v___x_6620_ = l_Lean_indentExpr(v_a_6536_);
                v___x_6621_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6621_, 0, v___x_6619_);
                lean_ctor_set(v___x_6621_, 1, v___x_6620_);
                v___x_6622_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_6621_, v___y_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_);
                lean_dec_ref(v___y_6617_);
                v_a_6623_ = lean_ctor_get(v___x_6622_, 0);
                v_isSharedCheck_6630_ = (!lean_is_exclusive(v___x_6622_)) as u8;
                if v_isSharedCheck_6630_ == 0 {
                    v___x_6625_ = v___x_6622_;
                    v_isShared_6626_ = v_isSharedCheck_6630_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_a_6623_);
                    lean_dec(v___x_6622_);
                    v___x_6625_ = lean_box(0);
                    v_isShared_6626_ = v_isSharedCheck_6630_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_6626_ == 0 {
                    v___x_6628_ = v___x_6625_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6629_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6629_, 0, v_a_6623_);
                    v___x_6628_ = v_reuseFailAlloc_6629_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6628_;
            }
            15 => {
                if v_isShared_6637_ == 0 {
                    v___x_6639_ = v___x_6636_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6640_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6640_, 0, v_a_6634_);
                    v___x_6639_ = v_reuseFailAlloc_6640_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6639_;
            }
            17 => {
                if v_isShared_6645_ == 0 {
                    v___x_6647_ = v___x_6644_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6648_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6648_, 0, v_a_6642_);
                    v___x_6647_ = v_reuseFailAlloc_6648_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0___boxed(
    mut v_stx_6650_: *mut LeanObject,
    mut v_a_6651_: *mut LeanObject,
    mut v_a_6652_: *mut LeanObject,
    mut v_a_6653_: *mut LeanObject,
    mut v_a_6654_: *mut LeanObject,
    mut v_a_6655_: *mut LeanObject,
    mut v_a_6656_: *mut LeanObject,
    mut v_a_6657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6658_: *mut LeanObject = core::ptr::null_mut();
    v_res_6658_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(v_stx_6650_, v_a_6651_, v_a_6652_, v_a_6653_, v_a_6654_, v_a_6655_, v_a_6656_);
    lean_dec(v_a_6656_);
    lean_dec_ref(v_a_6655_);
    lean_dec(v_a_6654_);
    lean_dec_ref(v_a_6653_);
    lean_dec(v_a_6652_);
    lean_dec_ref(v_a_6651_);
    return v_res_6658_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0(
    mut v_config_6661_: *mut LeanObject,
    mut v_item_6662_: *mut LeanObject,
    mut v___y_6663_: *mut LeanObject,
    mut v___y_6664_: *mut LeanObject,
    mut v___y_6665_: *mut LeanObject,
    mut v___y_6666_: *mut LeanObject,
    mut v___y_6667_: *mut LeanObject,
    mut v___y_6668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_item_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: u8 = 0;
    let mut v___x_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: u8 = 0;
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: u8 = 0;
    let mut v___x_6689_: u8 = 0;
    let mut v___x_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: u8 = 0;
    let mut v___x_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: u8 = 0;
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: u8 = 0;
    let mut v___x_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6701_: u8 = 0;
    let mut v_proofs_6702_: u8 = 0;
    let mut v_types_6703_: u8 = 0;
    let mut v_implicits_6704_: u8 = 0;
    let mut v_descend_6705_: u8 = 0;
    let mut v_underBinder_6706_: u8 = 0;
    let mut v_merge_6707_: u8 = 0;
    let mut v_useContext_6708_: u8 = 0;
    let mut v_onlyGivenNames_6709_: u8 = 0;
    let mut v_preserveBinderNames_6710_: u8 = 0;
    let mut v_lift_6711_: u8 = 0;
    let mut v___x_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6714_: u8 = 0;
    let mut v___x_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: u8 = 0;
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6722_: u8 = 0;
    let mut v_isSharedCheck_6723_: u8 = 0;
    let mut v_a_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6727_: u8 = 0;
    let mut v___x_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6731_: u8 = 0;
    let mut v_a_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6735_: u8 = 0;
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6739_: u8 = 0;
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: u8 = 0;
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6747_: u8 = 0;
    let mut v_proofs_6748_: u8 = 0;
    let mut v_types_6749_: u8 = 0;
    let mut v_implicits_6750_: u8 = 0;
    let mut v_descend_6751_: u8 = 0;
    let mut v_underBinder_6752_: u8 = 0;
    let mut v_usedOnly_6753_: u8 = 0;
    let mut v_merge_6754_: u8 = 0;
    let mut v_onlyGivenNames_6755_: u8 = 0;
    let mut v_preserveBinderNames_6756_: u8 = 0;
    let mut v_lift_6757_: u8 = 0;
    let mut v___x_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6760_: u8 = 0;
    let mut v___x_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: u8 = 0;
    let mut v___x_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6768_: u8 = 0;
    let mut v_isSharedCheck_6769_: u8 = 0;
    let mut v_a_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6773_: u8 = 0;
    let mut v___x_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6777_: u8 = 0;
    let mut v_a_6778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6781_: u8 = 0;
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6785_: u8 = 0;
    let mut v___x_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: u8 = 0;
    let mut v___x_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6793_: u8 = 0;
    let mut v_proofs_6794_: u8 = 0;
    let mut v_types_6795_: u8 = 0;
    let mut v_implicits_6796_: u8 = 0;
    let mut v_descend_6797_: u8 = 0;
    let mut v_usedOnly_6798_: u8 = 0;
    let mut v_merge_6799_: u8 = 0;
    let mut v_useContext_6800_: u8 = 0;
    let mut v_onlyGivenNames_6801_: u8 = 0;
    let mut v_preserveBinderNames_6802_: u8 = 0;
    let mut v_lift_6803_: u8 = 0;
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6806_: u8 = 0;
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: u8 = 0;
    let mut v___x_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6814_: u8 = 0;
    let mut v_isSharedCheck_6815_: u8 = 0;
    let mut v_a_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6819_: u8 = 0;
    let mut v___x_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6823_: u8 = 0;
    let mut v_a_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6827_: u8 = 0;
    let mut v___x_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6831_: u8 = 0;
    let mut v___x_6832_: u8 = 0;
    let mut v___x_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: u8 = 0;
    let mut v___x_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: u8 = 0;
    let mut v___x_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: u8 = 0;
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6844_: u8 = 0;
    let mut v_proofs_6845_: u8 = 0;
    let mut v_implicits_6846_: u8 = 0;
    let mut v_descend_6847_: u8 = 0;
    let mut v_underBinder_6848_: u8 = 0;
    let mut v_usedOnly_6849_: u8 = 0;
    let mut v_merge_6850_: u8 = 0;
    let mut v_useContext_6851_: u8 = 0;
    let mut v_onlyGivenNames_6852_: u8 = 0;
    let mut v_preserveBinderNames_6853_: u8 = 0;
    let mut v_lift_6854_: u8 = 0;
    let mut v___x_6856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6857_: u8 = 0;
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: u8 = 0;
    let mut v___x_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6865_: u8 = 0;
    let mut v_isSharedCheck_6866_: u8 = 0;
    let mut v_a_6867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6870_: u8 = 0;
    let mut v___x_6872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6874_: u8 = 0;
    let mut v_a_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6878_: u8 = 0;
    let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6882_: u8 = 0;
    let mut v___x_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: u8 = 0;
    let mut v___x_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6890_: u8 = 0;
    let mut v_types_6891_: u8 = 0;
    let mut v_implicits_6892_: u8 = 0;
    let mut v_descend_6893_: u8 = 0;
    let mut v_underBinder_6894_: u8 = 0;
    let mut v_usedOnly_6895_: u8 = 0;
    let mut v_merge_6896_: u8 = 0;
    let mut v_useContext_6897_: u8 = 0;
    let mut v_onlyGivenNames_6898_: u8 = 0;
    let mut v_preserveBinderNames_6899_: u8 = 0;
    let mut v_lift_6900_: u8 = 0;
    let mut v___x_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6903_: u8 = 0;
    let mut v___x_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: u8 = 0;
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6911_: u8 = 0;
    let mut v_isSharedCheck_6912_: u8 = 0;
    let mut v_a_6913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6916_: u8 = 0;
    let mut v___x_6918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6920_: u8 = 0;
    let mut v_a_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6924_: u8 = 0;
    let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6928_: u8 = 0;
    let mut v___x_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: u8 = 0;
    let mut v___x_6932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6936_: u8 = 0;
    let mut v_proofs_6937_: u8 = 0;
    let mut v_types_6938_: u8 = 0;
    let mut v_implicits_6939_: u8 = 0;
    let mut v_descend_6940_: u8 = 0;
    let mut v_underBinder_6941_: u8 = 0;
    let mut v_usedOnly_6942_: u8 = 0;
    let mut v_merge_6943_: u8 = 0;
    let mut v_useContext_6944_: u8 = 0;
    let mut v_onlyGivenNames_6945_: u8 = 0;
    let mut v_lift_6946_: u8 = 0;
    let mut v___x_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6949_: u8 = 0;
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: u8 = 0;
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6957_: u8 = 0;
    let mut v_isSharedCheck_6958_: u8 = 0;
    let mut v_a_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6962_: u8 = 0;
    let mut v___x_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6966_: u8 = 0;
    let mut v_a_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6970_: u8 = 0;
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6974_: u8 = 0;
    let mut v___x_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: u8 = 0;
    let mut v___x_6977_: u8 = 0;
    let mut v___x_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: u8 = 0;
    let mut v___x_6980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: u8 = 0;
    let mut v___x_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: u8 = 0;
    let mut v___x_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6989_: u8 = 0;
    let mut v_proofs_6990_: u8 = 0;
    let mut v_types_6991_: u8 = 0;
    let mut v_implicits_6992_: u8 = 0;
    let mut v_descend_6993_: u8 = 0;
    let mut v_underBinder_6994_: u8 = 0;
    let mut v_usedOnly_6995_: u8 = 0;
    let mut v_merge_6996_: u8 = 0;
    let mut v_useContext_6997_: u8 = 0;
    let mut v_preserveBinderNames_6998_: u8 = 0;
    let mut v_lift_6999_: u8 = 0;
    let mut v___x_7001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7002_: u8 = 0;
    let mut v___x_7004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: u8 = 0;
    let mut v___x_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7010_: u8 = 0;
    let mut v_isSharedCheck_7011_: u8 = 0;
    let mut v_a_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7015_: u8 = 0;
    let mut v___x_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7019_: u8 = 0;
    let mut v_a_7020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7023_: u8 = 0;
    let mut v___x_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7027_: u8 = 0;
    let mut v___x_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: u8 = 0;
    let mut v___x_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7035_: u8 = 0;
    let mut v_proofs_7036_: u8 = 0;
    let mut v_types_7037_: u8 = 0;
    let mut v_implicits_7038_: u8 = 0;
    let mut v_descend_7039_: u8 = 0;
    let mut v_underBinder_7040_: u8 = 0;
    let mut v_usedOnly_7041_: u8 = 0;
    let mut v_useContext_7042_: u8 = 0;
    let mut v_onlyGivenNames_7043_: u8 = 0;
    let mut v_preserveBinderNames_7044_: u8 = 0;
    let mut v_lift_7045_: u8 = 0;
    let mut v___x_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7048_: u8 = 0;
    let mut v___x_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: u8 = 0;
    let mut v___x_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7056_: u8 = 0;
    let mut v_isSharedCheck_7057_: u8 = 0;
    let mut v_a_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7061_: u8 = 0;
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7065_: u8 = 0;
    let mut v_a_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7069_: u8 = 0;
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7073_: u8 = 0;
    let mut v___x_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: u8 = 0;
    let mut v___x_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7081_: u8 = 0;
    let mut v_proofs_7082_: u8 = 0;
    let mut v_types_7083_: u8 = 0;
    let mut v_implicits_7084_: u8 = 0;
    let mut v_descend_7085_: u8 = 0;
    let mut v_underBinder_7086_: u8 = 0;
    let mut v_usedOnly_7087_: u8 = 0;
    let mut v_merge_7088_: u8 = 0;
    let mut v_useContext_7089_: u8 = 0;
    let mut v_onlyGivenNames_7090_: u8 = 0;
    let mut v_preserveBinderNames_7091_: u8 = 0;
    let mut v___x_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7094_: u8 = 0;
    let mut v___x_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7097_: u8 = 0;
    let mut v___x_7099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7102_: u8 = 0;
    let mut v_isSharedCheck_7103_: u8 = 0;
    let mut v_a_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7107_: u8 = 0;
    let mut v___x_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7111_: u8 = 0;
    let mut v_a_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7115_: u8 = 0;
    let mut v___x_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7119_: u8 = 0;
    let mut v___x_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: u8 = 0;
    let mut v___x_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: u8 = 0;
    let mut v___x_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7125_: u8 = 0;
    let mut v___x_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: u8 = 0;
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7133_: u8 = 0;
    let mut v_proofs_7134_: u8 = 0;
    let mut v_types_7135_: u8 = 0;
    let mut v_descend_7136_: u8 = 0;
    let mut v_underBinder_7137_: u8 = 0;
    let mut v_usedOnly_7138_: u8 = 0;
    let mut v_merge_7139_: u8 = 0;
    let mut v_useContext_7140_: u8 = 0;
    let mut v_onlyGivenNames_7141_: u8 = 0;
    let mut v_preserveBinderNames_7142_: u8 = 0;
    let mut v_lift_7143_: u8 = 0;
    let mut v___x_7145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7146_: u8 = 0;
    let mut v___x_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: u8 = 0;
    let mut v___x_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7154_: u8 = 0;
    let mut v_isSharedCheck_7155_: u8 = 0;
    let mut v_a_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7159_: u8 = 0;
    let mut v___x_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7163_: u8 = 0;
    let mut v_a_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7167_: u8 = 0;
    let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7171_: u8 = 0;
    let mut v___x_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: u8 = 0;
    let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7179_: u8 = 0;
    let mut v_proofs_7180_: u8 = 0;
    let mut v_types_7181_: u8 = 0;
    let mut v_implicits_7182_: u8 = 0;
    let mut v_underBinder_7183_: u8 = 0;
    let mut v_usedOnly_7184_: u8 = 0;
    let mut v_merge_7185_: u8 = 0;
    let mut v_useContext_7186_: u8 = 0;
    let mut v_onlyGivenNames_7187_: u8 = 0;
    let mut v_preserveBinderNames_7188_: u8 = 0;
    let mut v_lift_7189_: u8 = 0;
    let mut v___x_7191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7192_: u8 = 0;
    let mut v___x_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: u8 = 0;
    let mut v___x_7197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7200_: u8 = 0;
    let mut v_isSharedCheck_7201_: u8 = 0;
    let mut v_a_7202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7205_: u8 = 0;
    let mut v___x_7207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7209_: u8 = 0;
    let mut v_a_7210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7213_: u8 = 0;
    let mut v___x_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7217_: u8 = 0;
    let mut v___x_7218_: u8 = 0;
    let mut v_value_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7224_: u8 = 0;
    let mut v___x_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6680_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2;
                v___x_6681_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(
                    v_item_6662_,
                    v___x_6680_,
                    v___y_6663_,
                    v___y_6664_,
                    v___y_6665_,
                    v___y_6666_,
                    v___y_6667_,
                    v___y_6668_,
                );
                if lean_obj_tag(v___x_6681_) == 0 {
                    lean_dec_ref_known(v___x_6681_, 1);
                    v___x_6682_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_6662_);
                    if v___x_6682_ == 0 {
                        v___x_6683_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_6662_);
                        lean_inc_ref(v_item_6662_);
                        v___x_6684_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_6662_);
                        v___x_6685_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__1;
                        v___x_6686_ = lean_string_dec_lt(v___x_6683_, v___x_6685_);
                        if v___x_6686_ == 0 {
                            v___x_6687_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__2;
                            v___x_6688_ = lean_string_dec_lt(v___x_6683_, v___x_6687_);
                            if v___x_6688_ == 0 {
                                v___x_6689_ = lean_string_dec_eq(v___x_6683_, v___x_6687_);
                                if v___x_6689_ == 0 {
                                    v___x_6690_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__3;
                                    v___x_6691_ = lean_string_dec_eq(v___x_6683_, v___x_6690_);
                                    if v___x_6691_ == 0 {
                                        v___x_6692_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__4;
                                        v___x_6693_ = lean_string_dec_eq(v___x_6683_, v___x_6692_);
                                        lean_dec_ref(v___x_6683_);
                                        if v___x_6693_ == 0 {
                                            lean_dec_ref(v_item_6662_);
                                            lean_dec_ref(v_config_6661_);
                                            v_item_6671_ = v___x_6684_;
                                            v___y_6672_ = v___y_6663_;
                                            v___y_6673_ = v___y_6664_;
                                            v___y_6674_ = v___y_6665_;
                                            v___y_6675_ = v___y_6666_;
                                            v___y_6676_ = v___y_6667_;
                                            v___y_6677_ = v___y_6668_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_6694_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__5;
                                            v___x_6695_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                    v_item_6662_,
                                                    v___x_6694_,
                                                    v___y_6663_,
                                                    v___y_6664_,
                                                    v___y_6665_,
                                                    v___y_6666_,
                                                    v___y_6667_,
                                                    v___y_6668_,
                                                );
                                            if lean_obj_tag(v___x_6695_) == 0 {
                                                lean_dec_ref_known(v___x_6695_, 1);
                                                v___x_6696_ =
                                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                        v___x_6684_,
                                                    );
                                                if v___x_6696_ == 0 {
                                                    lean_dec_ref(v_item_6662_);
                                                    lean_dec_ref(v_config_6661_);
                                                    v_item_6671_ = v___x_6684_;
                                                    v___y_6672_ = v___y_6663_;
                                                    v___y_6673_ = v___y_6664_;
                                                    v___y_6674_ = v___y_6665_;
                                                    v___y_6675_ = v___y_6666_;
                                                    v___y_6676_ = v___y_6667_;
                                                    v___y_6677_ = v___y_6668_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec_ref(v___x_6684_);
                                                    v___x_6697_ =
                                                        l_Lean_Elab_ConfigEval_evalBoolItem(
                                                            v_item_6662_,
                                                            v___y_6663_,
                                                            v___y_6664_,
                                                            v___y_6665_,
                                                            v___y_6666_,
                                                            v___y_6667_,
                                                            v___y_6668_,
                                                        );
                                                    if lean_obj_tag(v___x_6697_) == 0 {
                                                        v_a_6698_ = lean_ctor_get(v___x_6697_, 0);
                                                        v_isSharedCheck_6723_ =
                                                            (!lean_is_exclusive(v___x_6697_)) as u8;
                                                        if v_isSharedCheck_6723_ == 0 {
                                                            v___x_6700_ = v___x_6697_;
                                                            v_isShared_6701_ =
                                                                v_isSharedCheck_6723_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_6698_);
                                                            lean_dec(v___x_6697_);
                                                            v___x_6700_ = lean_box(0);
                                                            v_isShared_6701_ =
                                                                v_isSharedCheck_6723_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_config_6661_);
                                                        v_a_6724_ = lean_ctor_get(v___x_6697_, 0);
                                                        v_isSharedCheck_6731_ =
                                                            (!lean_is_exclusive(v___x_6697_)) as u8;
                                                        if v_isSharedCheck_6731_ == 0 {
                                                            v___x_6726_ = v___x_6697_;
                                                            v_isShared_6727_ =
                                                                v_isSharedCheck_6731_;
                                                            state = 6;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_6724_);
                                                            lean_dec(v___x_6697_);
                                                            v___x_6726_ = lean_box(0);
                                                            v_isShared_6727_ =
                                                                v_isSharedCheck_6731_;
                                                            state = 6;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_6684_);
                                                lean_dec_ref(v_item_6662_);
                                                lean_dec_ref(v_config_6661_);
                                                v_a_6732_ = lean_ctor_get(v___x_6695_, 0);
                                                v_isSharedCheck_6739_ =
                                                    (!lean_is_exclusive(v___x_6695_)) as u8;
                                                if v_isSharedCheck_6739_ == 0 {
                                                    v___x_6734_ = v___x_6695_;
                                                    v_isShared_6735_ = v_isSharedCheck_6739_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_6732_);
                                                    lean_dec(v___x_6695_);
                                                    v___x_6734_ = lean_box(0);
                                                    v_isShared_6735_ = v_isSharedCheck_6739_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_6683_);
                                        v___x_6740_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__6;
                                        v___x_6741_ =
                                            l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                v_item_6662_,
                                                v___x_6740_,
                                                v___y_6663_,
                                                v___y_6664_,
                                                v___y_6665_,
                                                v___y_6666_,
                                                v___y_6667_,
                                                v___y_6668_,
                                            );
                                        if lean_obj_tag(v___x_6741_) == 0 {
                                            lean_dec_ref_known(v___x_6741_, 1);
                                            v___x_6742_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                    v___x_6684_,
                                                );
                                            if v___x_6742_ == 0 {
                                                lean_dec_ref(v_item_6662_);
                                                lean_dec_ref(v_config_6661_);
                                                v_item_6671_ = v___x_6684_;
                                                v___y_6672_ = v___y_6663_;
                                                v___y_6673_ = v___y_6664_;
                                                v___y_6674_ = v___y_6665_;
                                                v___y_6675_ = v___y_6666_;
                                                v___y_6676_ = v___y_6667_;
                                                v___y_6677_ = v___y_6668_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec_ref(v___x_6684_);
                                                v___x_6743_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                    v_item_6662_,
                                                    v___y_6663_,
                                                    v___y_6664_,
                                                    v___y_6665_,
                                                    v___y_6666_,
                                                    v___y_6667_,
                                                    v___y_6668_,
                                                );
                                                if lean_obj_tag(v___x_6743_) == 0 {
                                                    v_a_6744_ = lean_ctor_get(v___x_6743_, 0);
                                                    v_isSharedCheck_6769_ =
                                                        (!lean_is_exclusive(v___x_6743_)) as u8;
                                                    if v_isSharedCheck_6769_ == 0 {
                                                        v___x_6746_ = v___x_6743_;
                                                        v_isShared_6747_ = v_isSharedCheck_6769_;
                                                        state = 10;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_6744_);
                                                        lean_dec(v___x_6743_);
                                                        v___x_6746_ = lean_box(0);
                                                        v_isShared_6747_ = v_isSharedCheck_6769_;
                                                        state = 10;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_config_6661_);
                                                    v_a_6770_ = lean_ctor_get(v___x_6743_, 0);
                                                    v_isSharedCheck_6777_ =
                                                        (!lean_is_exclusive(v___x_6743_)) as u8;
                                                    if v_isSharedCheck_6777_ == 0 {
                                                        v___x_6772_ = v___x_6743_;
                                                        v_isShared_6773_ = v_isSharedCheck_6777_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_6770_);
                                                        lean_dec(v___x_6743_);
                                                        v___x_6772_ = lean_box(0);
                                                        v_isShared_6773_ = v_isSharedCheck_6777_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_6684_);
                                            lean_dec_ref(v_item_6662_);
                                            lean_dec_ref(v_config_6661_);
                                            v_a_6778_ = lean_ctor_get(v___x_6741_, 0);
                                            v_isSharedCheck_6785_ =
                                                (!lean_is_exclusive(v___x_6741_)) as u8;
                                            if v_isSharedCheck_6785_ == 0 {
                                                v___x_6780_ = v___x_6741_;
                                                v_isShared_6781_ = v_isSharedCheck_6785_;
                                                state = 16;
                                                continue;
                                            } else {
                                                lean_inc(v_a_6778_);
                                                lean_dec(v___x_6741_);
                                                v___x_6780_ = lean_box(0);
                                                v_isShared_6781_ = v_isSharedCheck_6785_;
                                                state = 16;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_6683_);
                                    v___x_6786_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__7;
                                    v___x_6787_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                        v_item_6662_,
                                        v___x_6786_,
                                        v___y_6663_,
                                        v___y_6664_,
                                        v___y_6665_,
                                        v___y_6666_,
                                        v___y_6667_,
                                        v___y_6668_,
                                    );
                                    if lean_obj_tag(v___x_6787_) == 0 {
                                        lean_dec_ref_known(v___x_6787_, 1);
                                        v___x_6788_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                            v___x_6684_,
                                        );
                                        if v___x_6788_ == 0 {
                                            lean_dec_ref(v_item_6662_);
                                            lean_dec_ref(v_config_6661_);
                                            v_item_6671_ = v___x_6684_;
                                            v___y_6672_ = v___y_6663_;
                                            v___y_6673_ = v___y_6664_;
                                            v___y_6674_ = v___y_6665_;
                                            v___y_6675_ = v___y_6666_;
                                            v___y_6676_ = v___y_6667_;
                                            v___y_6677_ = v___y_6668_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec_ref(v___x_6684_);
                                            v___x_6789_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                v_item_6662_,
                                                v___y_6663_,
                                                v___y_6664_,
                                                v___y_6665_,
                                                v___y_6666_,
                                                v___y_6667_,
                                                v___y_6668_,
                                            );
                                            if lean_obj_tag(v___x_6789_) == 0 {
                                                v_a_6790_ = lean_ctor_get(v___x_6789_, 0);
                                                v_isSharedCheck_6815_ =
                                                    (!lean_is_exclusive(v___x_6789_)) as u8;
                                                if v_isSharedCheck_6815_ == 0 {
                                                    v___x_6792_ = v___x_6789_;
                                                    v_isShared_6793_ = v_isSharedCheck_6815_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_6790_);
                                                    lean_dec(v___x_6789_);
                                                    v___x_6792_ = lean_box(0);
                                                    v_isShared_6793_ = v_isSharedCheck_6815_;
                                                    state = 18;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_config_6661_);
                                                v_a_6816_ = lean_ctor_get(v___x_6789_, 0);
                                                v_isSharedCheck_6823_ =
                                                    (!lean_is_exclusive(v___x_6789_)) as u8;
                                                if v_isSharedCheck_6823_ == 0 {
                                                    v___x_6818_ = v___x_6789_;
                                                    v_isShared_6819_ = v_isSharedCheck_6823_;
                                                    state = 22;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_6816_);
                                                    lean_dec(v___x_6789_);
                                                    v___x_6818_ = lean_box(0);
                                                    v_isShared_6819_ = v_isSharedCheck_6823_;
                                                    state = 22;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_6684_);
                                        lean_dec_ref(v_item_6662_);
                                        lean_dec_ref(v_config_6661_);
                                        v_a_6824_ = lean_ctor_get(v___x_6787_, 0);
                                        v_isSharedCheck_6831_ =
                                            (!lean_is_exclusive(v___x_6787_)) as u8;
                                        if v_isSharedCheck_6831_ == 0 {
                                            v___x_6826_ = v___x_6787_;
                                            v_isShared_6827_ = v_isSharedCheck_6831_;
                                            state = 24;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6824_);
                                            lean_dec(v___x_6787_);
                                            v___x_6826_ = lean_box(0);
                                            v_isShared_6827_ = v_isSharedCheck_6831_;
                                            state = 24;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_6832_ = lean_string_dec_eq(v___x_6683_, v___x_6685_);
                                if v___x_6832_ == 0 {
                                    v___x_6833_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__8;
                                    v___x_6834_ = lean_string_dec_eq(v___x_6683_, v___x_6833_);
                                    if v___x_6834_ == 0 {
                                        v___x_6835_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__9;
                                        v___x_6836_ = lean_string_dec_eq(v___x_6683_, v___x_6835_);
                                        lean_dec_ref(v___x_6683_);
                                        if v___x_6836_ == 0 {
                                            lean_dec_ref(v_item_6662_);
                                            lean_dec_ref(v_config_6661_);
                                            v_item_6671_ = v___x_6684_;
                                            v___y_6672_ = v___y_6663_;
                                            v___y_6673_ = v___y_6664_;
                                            v___y_6674_ = v___y_6665_;
                                            v___y_6675_ = v___y_6666_;
                                            v___y_6676_ = v___y_6667_;
                                            v___y_6677_ = v___y_6668_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_6837_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__10;
                                            v___x_6838_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                    v_item_6662_,
                                                    v___x_6837_,
                                                    v___y_6663_,
                                                    v___y_6664_,
                                                    v___y_6665_,
                                                    v___y_6666_,
                                                    v___y_6667_,
                                                    v___y_6668_,
                                                );
                                            if lean_obj_tag(v___x_6838_) == 0 {
                                                lean_dec_ref_known(v___x_6838_, 1);
                                                v___x_6839_ =
                                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                        v___x_6684_,
                                                    );
                                                if v___x_6839_ == 0 {
                                                    lean_dec_ref(v_item_6662_);
                                                    lean_dec_ref(v_config_6661_);
                                                    v_item_6671_ = v___x_6684_;
                                                    v___y_6672_ = v___y_6663_;
                                                    v___y_6673_ = v___y_6664_;
                                                    v___y_6674_ = v___y_6665_;
                                                    v___y_6675_ = v___y_6666_;
                                                    v___y_6676_ = v___y_6667_;
                                                    v___y_6677_ = v___y_6668_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec_ref(v___x_6684_);
                                                    v___x_6840_ =
                                                        l_Lean_Elab_ConfigEval_evalBoolItem(
                                                            v_item_6662_,
                                                            v___y_6663_,
                                                            v___y_6664_,
                                                            v___y_6665_,
                                                            v___y_6666_,
                                                            v___y_6667_,
                                                            v___y_6668_,
                                                        );
                                                    if lean_obj_tag(v___x_6840_) == 0 {
                                                        v_a_6841_ = lean_ctor_get(v___x_6840_, 0);
                                                        v_isSharedCheck_6866_ =
                                                            (!lean_is_exclusive(v___x_6840_)) as u8;
                                                        if v_isSharedCheck_6866_ == 0 {
                                                            v___x_6843_ = v___x_6840_;
                                                            v_isShared_6844_ =
                                                                v_isSharedCheck_6866_;
                                                            state = 26;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_6841_);
                                                            lean_dec(v___x_6840_);
                                                            v___x_6843_ = lean_box(0);
                                                            v_isShared_6844_ =
                                                                v_isSharedCheck_6866_;
                                                            state = 26;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_config_6661_);
                                                        v_a_6867_ = lean_ctor_get(v___x_6840_, 0);
                                                        v_isSharedCheck_6874_ =
                                                            (!lean_is_exclusive(v___x_6840_)) as u8;
                                                        if v_isSharedCheck_6874_ == 0 {
                                                            v___x_6869_ = v___x_6840_;
                                                            v_isShared_6870_ =
                                                                v_isSharedCheck_6874_;
                                                            state = 30;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_6867_);
                                                            lean_dec(v___x_6840_);
                                                            v___x_6869_ = lean_box(0);
                                                            v_isShared_6870_ =
                                                                v_isSharedCheck_6874_;
                                                            state = 30;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_6684_);
                                                lean_dec_ref(v_item_6662_);
                                                lean_dec_ref(v_config_6661_);
                                                v_a_6875_ = lean_ctor_get(v___x_6838_, 0);
                                                v_isSharedCheck_6882_ =
                                                    (!lean_is_exclusive(v___x_6838_)) as u8;
                                                if v_isSharedCheck_6882_ == 0 {
                                                    v___x_6877_ = v___x_6838_;
                                                    v_isShared_6878_ = v_isSharedCheck_6882_;
                                                    state = 32;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_6875_);
                                                    lean_dec(v___x_6838_);
                                                    v___x_6877_ = lean_box(0);
                                                    v_isShared_6878_ = v_isSharedCheck_6882_;
                                                    state = 32;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_6683_);
                                        v___x_6883_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__11;
                                        v___x_6884_ =
                                            l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                v_item_6662_,
                                                v___x_6883_,
                                                v___y_6663_,
                                                v___y_6664_,
                                                v___y_6665_,
                                                v___y_6666_,
                                                v___y_6667_,
                                                v___y_6668_,
                                            );
                                        if lean_obj_tag(v___x_6884_) == 0 {
                                            lean_dec_ref_known(v___x_6884_, 1);
                                            v___x_6885_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                    v___x_6684_,
                                                );
                                            if v___x_6885_ == 0 {
                                                lean_dec_ref(v_item_6662_);
                                                lean_dec_ref(v_config_6661_);
                                                v_item_6671_ = v___x_6684_;
                                                v___y_6672_ = v___y_6663_;
                                                v___y_6673_ = v___y_6664_;
                                                v___y_6674_ = v___y_6665_;
                                                v___y_6675_ = v___y_6666_;
                                                v___y_6676_ = v___y_6667_;
                                                v___y_6677_ = v___y_6668_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec_ref(v___x_6684_);
                                                v___x_6886_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                    v_item_6662_,
                                                    v___y_6663_,
                                                    v___y_6664_,
                                                    v___y_6665_,
                                                    v___y_6666_,
                                                    v___y_6667_,
                                                    v___y_6668_,
                                                );
                                                if lean_obj_tag(v___x_6886_) == 0 {
                                                    v_a_6887_ = lean_ctor_get(v___x_6886_, 0);
                                                    v_isSharedCheck_6912_ =
                                                        (!lean_is_exclusive(v___x_6886_)) as u8;
                                                    if v_isSharedCheck_6912_ == 0 {
                                                        v___x_6889_ = v___x_6886_;
                                                        v_isShared_6890_ = v_isSharedCheck_6912_;
                                                        state = 34;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_6887_);
                                                        lean_dec(v___x_6886_);
                                                        v___x_6889_ = lean_box(0);
                                                        v_isShared_6890_ = v_isSharedCheck_6912_;
                                                        state = 34;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_config_6661_);
                                                    v_a_6913_ = lean_ctor_get(v___x_6886_, 0);
                                                    v_isSharedCheck_6920_ =
                                                        (!lean_is_exclusive(v___x_6886_)) as u8;
                                                    if v_isSharedCheck_6920_ == 0 {
                                                        v___x_6915_ = v___x_6886_;
                                                        v_isShared_6916_ = v_isSharedCheck_6920_;
                                                        state = 38;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_6913_);
                                                        lean_dec(v___x_6886_);
                                                        v___x_6915_ = lean_box(0);
                                                        v_isShared_6916_ = v_isSharedCheck_6920_;
                                                        state = 38;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_6684_);
                                            lean_dec_ref(v_item_6662_);
                                            lean_dec_ref(v_config_6661_);
                                            v_a_6921_ = lean_ctor_get(v___x_6884_, 0);
                                            v_isSharedCheck_6928_ =
                                                (!lean_is_exclusive(v___x_6884_)) as u8;
                                            if v_isSharedCheck_6928_ == 0 {
                                                v___x_6923_ = v___x_6884_;
                                                v_isShared_6924_ = v_isSharedCheck_6928_;
                                                state = 40;
                                                continue;
                                            } else {
                                                lean_inc(v_a_6921_);
                                                lean_dec(v___x_6884_);
                                                v___x_6923_ = lean_box(0);
                                                v_isShared_6924_ = v_isSharedCheck_6928_;
                                                state = 40;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_6683_);
                                    v___x_6929_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__12;
                                    v___x_6930_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                        v_item_6662_,
                                        v___x_6929_,
                                        v___y_6663_,
                                        v___y_6664_,
                                        v___y_6665_,
                                        v___y_6666_,
                                        v___y_6667_,
                                        v___y_6668_,
                                    );
                                    if lean_obj_tag(v___x_6930_) == 0 {
                                        lean_dec_ref_known(v___x_6930_, 1);
                                        v___x_6931_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                            v___x_6684_,
                                        );
                                        if v___x_6931_ == 0 {
                                            lean_dec_ref(v_item_6662_);
                                            lean_dec_ref(v_config_6661_);
                                            v_item_6671_ = v___x_6684_;
                                            v___y_6672_ = v___y_6663_;
                                            v___y_6673_ = v___y_6664_;
                                            v___y_6674_ = v___y_6665_;
                                            v___y_6675_ = v___y_6666_;
                                            v___y_6676_ = v___y_6667_;
                                            v___y_6677_ = v___y_6668_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec_ref(v___x_6684_);
                                            v___x_6932_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                v_item_6662_,
                                                v___y_6663_,
                                                v___y_6664_,
                                                v___y_6665_,
                                                v___y_6666_,
                                                v___y_6667_,
                                                v___y_6668_,
                                            );
                                            if lean_obj_tag(v___x_6932_) == 0 {
                                                v_a_6933_ = lean_ctor_get(v___x_6932_, 0);
                                                v_isSharedCheck_6958_ =
                                                    (!lean_is_exclusive(v___x_6932_)) as u8;
                                                if v_isSharedCheck_6958_ == 0 {
                                                    v___x_6935_ = v___x_6932_;
                                                    v_isShared_6936_ = v_isSharedCheck_6958_;
                                                    state = 42;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_6933_);
                                                    lean_dec(v___x_6932_);
                                                    v___x_6935_ = lean_box(0);
                                                    v_isShared_6936_ = v_isSharedCheck_6958_;
                                                    state = 42;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_config_6661_);
                                                v_a_6959_ = lean_ctor_get(v___x_6932_, 0);
                                                v_isSharedCheck_6966_ =
                                                    (!lean_is_exclusive(v___x_6932_)) as u8;
                                                if v_isSharedCheck_6966_ == 0 {
                                                    v___x_6961_ = v___x_6932_;
                                                    v_isShared_6962_ = v_isSharedCheck_6966_;
                                                    state = 46;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_6959_);
                                                    lean_dec(v___x_6932_);
                                                    v___x_6961_ = lean_box(0);
                                                    v_isShared_6962_ = v_isSharedCheck_6966_;
                                                    state = 46;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_6684_);
                                        lean_dec_ref(v_item_6662_);
                                        lean_dec_ref(v_config_6661_);
                                        v_a_6967_ = lean_ctor_get(v___x_6930_, 0);
                                        v_isSharedCheck_6974_ =
                                            (!lean_is_exclusive(v___x_6930_)) as u8;
                                        if v_isSharedCheck_6974_ == 0 {
                                            v___x_6969_ = v___x_6930_;
                                            v_isShared_6970_ = v_isSharedCheck_6974_;
                                            state = 48;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6967_);
                                            lean_dec(v___x_6930_);
                                            v___x_6969_ = lean_box(0);
                                            v_isShared_6970_ = v_isSharedCheck_6974_;
                                            state = 48;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_6975_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__13;
                            v___x_6976_ = lean_string_dec_lt(v___x_6683_, v___x_6975_);
                            if v___x_6976_ == 0 {
                                v___x_6977_ = lean_string_dec_eq(v___x_6683_, v___x_6975_);
                                if v___x_6977_ == 0 {
                                    v___x_6978_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__14;
                                    v___x_6979_ = lean_string_dec_eq(v___x_6683_, v___x_6978_);
                                    if v___x_6979_ == 0 {
                                        v___x_6980_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__15;
                                        v___x_6981_ = lean_string_dec_eq(v___x_6683_, v___x_6980_);
                                        lean_dec_ref(v___x_6683_);
                                        if v___x_6981_ == 0 {
                                            lean_dec_ref(v_item_6662_);
                                            lean_dec_ref(v_config_6661_);
                                            v_item_6671_ = v___x_6684_;
                                            v___y_6672_ = v___y_6663_;
                                            v___y_6673_ = v___y_6664_;
                                            v___y_6674_ = v___y_6665_;
                                            v___y_6675_ = v___y_6666_;
                                            v___y_6676_ = v___y_6667_;
                                            v___y_6677_ = v___y_6668_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_6982_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__16;
                                            v___x_6983_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                    v_item_6662_,
                                                    v___x_6982_,
                                                    v___y_6663_,
                                                    v___y_6664_,
                                                    v___y_6665_,
                                                    v___y_6666_,
                                                    v___y_6667_,
                                                    v___y_6668_,
                                                );
                                            if lean_obj_tag(v___x_6983_) == 0 {
                                                lean_dec_ref_known(v___x_6983_, 1);
                                                v___x_6984_ =
                                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                        v___x_6684_,
                                                    );
                                                if v___x_6984_ == 0 {
                                                    lean_dec_ref(v_item_6662_);
                                                    lean_dec_ref(v_config_6661_);
                                                    v_item_6671_ = v___x_6684_;
                                                    v___y_6672_ = v___y_6663_;
                                                    v___y_6673_ = v___y_6664_;
                                                    v___y_6674_ = v___y_6665_;
                                                    v___y_6675_ = v___y_6666_;
                                                    v___y_6676_ = v___y_6667_;
                                                    v___y_6677_ = v___y_6668_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec_ref(v___x_6684_);
                                                    v___x_6985_ =
                                                        l_Lean_Elab_ConfigEval_evalBoolItem(
                                                            v_item_6662_,
                                                            v___y_6663_,
                                                            v___y_6664_,
                                                            v___y_6665_,
                                                            v___y_6666_,
                                                            v___y_6667_,
                                                            v___y_6668_,
                                                        );
                                                    if lean_obj_tag(v___x_6985_) == 0 {
                                                        v_a_6986_ = lean_ctor_get(v___x_6985_, 0);
                                                        v_isSharedCheck_7011_ =
                                                            (!lean_is_exclusive(v___x_6985_)) as u8;
                                                        if v_isSharedCheck_7011_ == 0 {
                                                            v___x_6988_ = v___x_6985_;
                                                            v_isShared_6989_ =
                                                                v_isSharedCheck_7011_;
                                                            state = 50;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_6986_);
                                                            lean_dec(v___x_6985_);
                                                            v___x_6988_ = lean_box(0);
                                                            v_isShared_6989_ =
                                                                v_isSharedCheck_7011_;
                                                            state = 50;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_config_6661_);
                                                        v_a_7012_ = lean_ctor_get(v___x_6985_, 0);
                                                        v_isSharedCheck_7019_ =
                                                            (!lean_is_exclusive(v___x_6985_)) as u8;
                                                        if v_isSharedCheck_7019_ == 0 {
                                                            v___x_7014_ = v___x_6985_;
                                                            v_isShared_7015_ =
                                                                v_isSharedCheck_7019_;
                                                            state = 54;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_7012_);
                                                            lean_dec(v___x_6985_);
                                                            v___x_7014_ = lean_box(0);
                                                            v_isShared_7015_ =
                                                                v_isSharedCheck_7019_;
                                                            state = 54;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_6684_);
                                                lean_dec_ref(v_item_6662_);
                                                lean_dec_ref(v_config_6661_);
                                                v_a_7020_ = lean_ctor_get(v___x_6983_, 0);
                                                v_isSharedCheck_7027_ =
                                                    (!lean_is_exclusive(v___x_6983_)) as u8;
                                                if v_isSharedCheck_7027_ == 0 {
                                                    v___x_7022_ = v___x_6983_;
                                                    v_isShared_7023_ = v_isSharedCheck_7027_;
                                                    state = 56;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_7020_);
                                                    lean_dec(v___x_6983_);
                                                    v___x_7022_ = lean_box(0);
                                                    v_isShared_7023_ = v_isSharedCheck_7027_;
                                                    state = 56;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_6683_);
                                        v___x_7028_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__17;
                                        v___x_7029_ =
                                            l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                v_item_6662_,
                                                v___x_7028_,
                                                v___y_6663_,
                                                v___y_6664_,
                                                v___y_6665_,
                                                v___y_6666_,
                                                v___y_6667_,
                                                v___y_6668_,
                                            );
                                        if lean_obj_tag(v___x_7029_) == 0 {
                                            lean_dec_ref_known(v___x_7029_, 1);
                                            v___x_7030_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                    v___x_6684_,
                                                );
                                            if v___x_7030_ == 0 {
                                                lean_dec_ref(v_item_6662_);
                                                lean_dec_ref(v_config_6661_);
                                                v_item_6671_ = v___x_6684_;
                                                v___y_6672_ = v___y_6663_;
                                                v___y_6673_ = v___y_6664_;
                                                v___y_6674_ = v___y_6665_;
                                                v___y_6675_ = v___y_6666_;
                                                v___y_6676_ = v___y_6667_;
                                                v___y_6677_ = v___y_6668_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec_ref(v___x_6684_);
                                                v___x_7031_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                    v_item_6662_,
                                                    v___y_6663_,
                                                    v___y_6664_,
                                                    v___y_6665_,
                                                    v___y_6666_,
                                                    v___y_6667_,
                                                    v___y_6668_,
                                                );
                                                if lean_obj_tag(v___x_7031_) == 0 {
                                                    v_a_7032_ = lean_ctor_get(v___x_7031_, 0);
                                                    v_isSharedCheck_7057_ =
                                                        (!lean_is_exclusive(v___x_7031_)) as u8;
                                                    if v_isSharedCheck_7057_ == 0 {
                                                        v___x_7034_ = v___x_7031_;
                                                        v_isShared_7035_ = v_isSharedCheck_7057_;
                                                        state = 58;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_7032_);
                                                        lean_dec(v___x_7031_);
                                                        v___x_7034_ = lean_box(0);
                                                        v_isShared_7035_ = v_isSharedCheck_7057_;
                                                        state = 58;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_config_6661_);
                                                    v_a_7058_ = lean_ctor_get(v___x_7031_, 0);
                                                    v_isSharedCheck_7065_ =
                                                        (!lean_is_exclusive(v___x_7031_)) as u8;
                                                    if v_isSharedCheck_7065_ == 0 {
                                                        v___x_7060_ = v___x_7031_;
                                                        v_isShared_7061_ = v_isSharedCheck_7065_;
                                                        state = 62;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_7058_);
                                                        lean_dec(v___x_7031_);
                                                        v___x_7060_ = lean_box(0);
                                                        v_isShared_7061_ = v_isSharedCheck_7065_;
                                                        state = 62;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_6684_);
                                            lean_dec_ref(v_item_6662_);
                                            lean_dec_ref(v_config_6661_);
                                            v_a_7066_ = lean_ctor_get(v___x_7029_, 0);
                                            v_isSharedCheck_7073_ =
                                                (!lean_is_exclusive(v___x_7029_)) as u8;
                                            if v_isSharedCheck_7073_ == 0 {
                                                v___x_7068_ = v___x_7029_;
                                                v_isShared_7069_ = v_isSharedCheck_7073_;
                                                state = 64;
                                                continue;
                                            } else {
                                                lean_inc(v_a_7066_);
                                                lean_dec(v___x_7029_);
                                                v___x_7068_ = lean_box(0);
                                                v_isShared_7069_ = v_isSharedCheck_7073_;
                                                state = 64;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_6683_);
                                    v___x_7074_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__18;
                                    v___x_7075_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                        v_item_6662_,
                                        v___x_7074_,
                                        v___y_6663_,
                                        v___y_6664_,
                                        v___y_6665_,
                                        v___y_6666_,
                                        v___y_6667_,
                                        v___y_6668_,
                                    );
                                    if lean_obj_tag(v___x_7075_) == 0 {
                                        lean_dec_ref_known(v___x_7075_, 1);
                                        v___x_7076_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                            v___x_6684_,
                                        );
                                        if v___x_7076_ == 0 {
                                            lean_dec_ref(v_item_6662_);
                                            lean_dec_ref(v_config_6661_);
                                            v_item_6671_ = v___x_6684_;
                                            v___y_6672_ = v___y_6663_;
                                            v___y_6673_ = v___y_6664_;
                                            v___y_6674_ = v___y_6665_;
                                            v___y_6675_ = v___y_6666_;
                                            v___y_6676_ = v___y_6667_;
                                            v___y_6677_ = v___y_6668_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec_ref(v___x_6684_);
                                            v___x_7077_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                v_item_6662_,
                                                v___y_6663_,
                                                v___y_6664_,
                                                v___y_6665_,
                                                v___y_6666_,
                                                v___y_6667_,
                                                v___y_6668_,
                                            );
                                            if lean_obj_tag(v___x_7077_) == 0 {
                                                v_a_7078_ = lean_ctor_get(v___x_7077_, 0);
                                                v_isSharedCheck_7103_ =
                                                    (!lean_is_exclusive(v___x_7077_)) as u8;
                                                if v_isSharedCheck_7103_ == 0 {
                                                    v___x_7080_ = v___x_7077_;
                                                    v_isShared_7081_ = v_isSharedCheck_7103_;
                                                    state = 66;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_7078_);
                                                    lean_dec(v___x_7077_);
                                                    v___x_7080_ = lean_box(0);
                                                    v_isShared_7081_ = v_isSharedCheck_7103_;
                                                    state = 66;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_config_6661_);
                                                v_a_7104_ = lean_ctor_get(v___x_7077_, 0);
                                                v_isSharedCheck_7111_ =
                                                    (!lean_is_exclusive(v___x_7077_)) as u8;
                                                if v_isSharedCheck_7111_ == 0 {
                                                    v___x_7106_ = v___x_7077_;
                                                    v_isShared_7107_ = v_isSharedCheck_7111_;
                                                    state = 70;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_7104_);
                                                    lean_dec(v___x_7077_);
                                                    v___x_7106_ = lean_box(0);
                                                    v_isShared_7107_ = v_isSharedCheck_7111_;
                                                    state = 70;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_6684_);
                                        lean_dec_ref(v_item_6662_);
                                        lean_dec_ref(v_config_6661_);
                                        v_a_7112_ = lean_ctor_get(v___x_7075_, 0);
                                        v_isSharedCheck_7119_ =
                                            (!lean_is_exclusive(v___x_7075_)) as u8;
                                        if v_isSharedCheck_7119_ == 0 {
                                            v___x_7114_ = v___x_7075_;
                                            v_isShared_7115_ = v_isSharedCheck_7119_;
                                            state = 72;
                                            continue;
                                        } else {
                                            lean_inc(v_a_7112_);
                                            lean_dec(v___x_7075_);
                                            v___x_7114_ = lean_box(0);
                                            v_isShared_7115_ = v_isSharedCheck_7119_;
                                            state = 72;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_7120_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__19;
                                v___x_7121_ = lean_string_dec_eq(v___x_6683_, v___x_7120_);
                                if v___x_7121_ == 0 {
                                    v___x_7122_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__20;
                                    v___x_7123_ = lean_string_dec_eq(v___x_6683_, v___x_7122_);
                                    if v___x_7123_ == 0 {
                                        v___x_7124_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__21;
                                        v___x_7125_ = lean_string_dec_eq(v___x_6683_, v___x_7124_);
                                        lean_dec_ref(v___x_6683_);
                                        if v___x_7125_ == 0 {
                                            lean_dec_ref(v_item_6662_);
                                            lean_dec_ref(v_config_6661_);
                                            v_item_6671_ = v___x_6684_;
                                            v___y_6672_ = v___y_6663_;
                                            v___y_6673_ = v___y_6664_;
                                            v___y_6674_ = v___y_6665_;
                                            v___y_6675_ = v___y_6666_;
                                            v___y_6676_ = v___y_6667_;
                                            v___y_6677_ = v___y_6668_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_7126_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__22;
                                            v___x_7127_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                    v_item_6662_,
                                                    v___x_7126_,
                                                    v___y_6663_,
                                                    v___y_6664_,
                                                    v___y_6665_,
                                                    v___y_6666_,
                                                    v___y_6667_,
                                                    v___y_6668_,
                                                );
                                            if lean_obj_tag(v___x_7127_) == 0 {
                                                lean_dec_ref_known(v___x_7127_, 1);
                                                v___x_7128_ =
                                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                        v___x_6684_,
                                                    );
                                                if v___x_7128_ == 0 {
                                                    lean_dec_ref(v_item_6662_);
                                                    lean_dec_ref(v_config_6661_);
                                                    v_item_6671_ = v___x_6684_;
                                                    v___y_6672_ = v___y_6663_;
                                                    v___y_6673_ = v___y_6664_;
                                                    v___y_6674_ = v___y_6665_;
                                                    v___y_6675_ = v___y_6666_;
                                                    v___y_6676_ = v___y_6667_;
                                                    v___y_6677_ = v___y_6668_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec_ref(v___x_6684_);
                                                    v___x_7129_ =
                                                        l_Lean_Elab_ConfigEval_evalBoolItem(
                                                            v_item_6662_,
                                                            v___y_6663_,
                                                            v___y_6664_,
                                                            v___y_6665_,
                                                            v___y_6666_,
                                                            v___y_6667_,
                                                            v___y_6668_,
                                                        );
                                                    if lean_obj_tag(v___x_7129_) == 0 {
                                                        v_a_7130_ = lean_ctor_get(v___x_7129_, 0);
                                                        v_isSharedCheck_7155_ =
                                                            (!lean_is_exclusive(v___x_7129_)) as u8;
                                                        if v_isSharedCheck_7155_ == 0 {
                                                            v___x_7132_ = v___x_7129_;
                                                            v_isShared_7133_ =
                                                                v_isSharedCheck_7155_;
                                                            state = 74;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_7130_);
                                                            lean_dec(v___x_7129_);
                                                            v___x_7132_ = lean_box(0);
                                                            v_isShared_7133_ =
                                                                v_isSharedCheck_7155_;
                                                            state = 74;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_config_6661_);
                                                        v_a_7156_ = lean_ctor_get(v___x_7129_, 0);
                                                        v_isSharedCheck_7163_ =
                                                            (!lean_is_exclusive(v___x_7129_)) as u8;
                                                        if v_isSharedCheck_7163_ == 0 {
                                                            v___x_7158_ = v___x_7129_;
                                                            v_isShared_7159_ =
                                                                v_isSharedCheck_7163_;
                                                            state = 78;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_7156_);
                                                            lean_dec(v___x_7129_);
                                                            v___x_7158_ = lean_box(0);
                                                            v_isShared_7159_ =
                                                                v_isSharedCheck_7163_;
                                                            state = 78;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_6684_);
                                                lean_dec_ref(v_item_6662_);
                                                lean_dec_ref(v_config_6661_);
                                                v_a_7164_ = lean_ctor_get(v___x_7127_, 0);
                                                v_isSharedCheck_7171_ =
                                                    (!lean_is_exclusive(v___x_7127_)) as u8;
                                                if v_isSharedCheck_7171_ == 0 {
                                                    v___x_7166_ = v___x_7127_;
                                                    v_isShared_7167_ = v_isSharedCheck_7171_;
                                                    state = 80;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_7164_);
                                                    lean_dec(v___x_7127_);
                                                    v___x_7166_ = lean_box(0);
                                                    v_isShared_7167_ = v_isSharedCheck_7171_;
                                                    state = 80;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_6683_);
                                        v___x_7172_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabExtractLetsConfig_evalConfigItem___lam__0___closed__23;
                                        v___x_7173_ =
                                            l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                v_item_6662_,
                                                v___x_7172_,
                                                v___y_6663_,
                                                v___y_6664_,
                                                v___y_6665_,
                                                v___y_6666_,
                                                v___y_6667_,
                                                v___y_6668_,
                                            );
                                        if lean_obj_tag(v___x_7173_) == 0 {
                                            lean_dec_ref_known(v___x_7173_, 1);
                                            v___x_7174_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                    v___x_6684_,
                                                );
                                            if v___x_7174_ == 0 {
                                                lean_dec_ref(v_item_6662_);
                                                lean_dec_ref(v_config_6661_);
                                                v_item_6671_ = v___x_6684_;
                                                v___y_6672_ = v___y_6663_;
                                                v___y_6673_ = v___y_6664_;
                                                v___y_6674_ = v___y_6665_;
                                                v___y_6675_ = v___y_6666_;
                                                v___y_6676_ = v___y_6667_;
                                                v___y_6677_ = v___y_6668_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec_ref(v___x_6684_);
                                                v___x_7175_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                    v_item_6662_,
                                                    v___y_6663_,
                                                    v___y_6664_,
                                                    v___y_6665_,
                                                    v___y_6666_,
                                                    v___y_6667_,
                                                    v___y_6668_,
                                                );
                                                if lean_obj_tag(v___x_7175_) == 0 {
                                                    v_a_7176_ = lean_ctor_get(v___x_7175_, 0);
                                                    v_isSharedCheck_7201_ =
                                                        (!lean_is_exclusive(v___x_7175_)) as u8;
                                                    if v_isSharedCheck_7201_ == 0 {
                                                        v___x_7178_ = v___x_7175_;
                                                        v_isShared_7179_ = v_isSharedCheck_7201_;
                                                        state = 82;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_7176_);
                                                        lean_dec(v___x_7175_);
                                                        v___x_7178_ = lean_box(0);
                                                        v_isShared_7179_ = v_isSharedCheck_7201_;
                                                        state = 82;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_config_6661_);
                                                    v_a_7202_ = lean_ctor_get(v___x_7175_, 0);
                                                    v_isSharedCheck_7209_ =
                                                        (!lean_is_exclusive(v___x_7175_)) as u8;
                                                    if v_isSharedCheck_7209_ == 0 {
                                                        v___x_7204_ = v___x_7175_;
                                                        v_isShared_7205_ = v_isSharedCheck_7209_;
                                                        state = 86;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_7202_);
                                                        lean_dec(v___x_7175_);
                                                        v___x_7204_ = lean_box(0);
                                                        v_isShared_7205_ = v_isSharedCheck_7209_;
                                                        state = 86;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_6684_);
                                            lean_dec_ref(v_item_6662_);
                                            lean_dec_ref(v_config_6661_);
                                            v_a_7210_ = lean_ctor_get(v___x_7173_, 0);
                                            v_isSharedCheck_7217_ =
                                                (!lean_is_exclusive(v___x_7173_)) as u8;
                                            if v_isSharedCheck_7217_ == 0 {
                                                v___x_7212_ = v___x_7173_;
                                                v_isShared_7213_ = v_isSharedCheck_7217_;
                                                state = 88;
                                                continue;
                                            } else {
                                                lean_inc(v_a_7210_);
                                                lean_dec(v___x_7173_);
                                                v___x_7212_ = lean_box(0);
                                                v_isShared_7213_ = v_isSharedCheck_7217_;
                                                state = 88;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_6683_);
                                    lean_dec_ref(v_config_6661_);
                                    v___x_7218_ =
                                        l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_6684_);
                                    if v___x_7218_ == 0 {
                                        lean_dec_ref(v_item_6662_);
                                        v_item_6671_ = v___x_6684_;
                                        v___y_6672_ = v___y_6663_;
                                        v___y_6673_ = v___y_6664_;
                                        v___y_6674_ = v___y_6665_;
                                        v___y_6675_ = v___y_6666_;
                                        v___y_6676_ = v___y_6667_;
                                        v___y_6677_ = v___y_6668_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec_ref(v___x_6684_);
                                        v_value_7219_ = lean_ctor_get(v_item_6662_, 2);
                                        lean_inc(v_value_7219_);
                                        lean_dec_ref(v_item_6662_);
                                        v___x_7220_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem_spec__0(v_value_7219_, v___y_6663_, v___y_6664_, v___y_6665_, v___y_6666_, v___y_6667_, v___y_6668_);
                                        return v___x_7220_;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_config_6661_);
                        v_item_6671_ = v_item_6662_;
                        v___y_6672_ = v___y_6663_;
                        v___y_6673_ = v___y_6664_;
                        v___y_6674_ = v___y_6665_;
                        v___y_6675_ = v___y_6666_;
                        v___y_6676_ = v___y_6667_;
                        v___y_6677_ = v___y_6668_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_item_6662_);
                    lean_dec_ref(v_config_6661_);
                    v_a_7221_ = lean_ctor_get(v___x_6681_, 0);
                    v_isSharedCheck_7228_ = (!lean_is_exclusive(v___x_6681_)) as u8;
                    if v_isSharedCheck_7228_ == 0 {
                        v___x_7223_ = v___x_6681_;
                        v_isShared_7224_ = v_isSharedCheck_7228_;
                        state = 90;
                        continue;
                    } else {
                        lean_inc(v_a_7221_);
                        lean_dec(v___x_6681_);
                        v___x_7223_ = lean_box(0);
                        v_isShared_7224_ = v_isSharedCheck_7228_;
                        state = 90;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6678_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___closed__0;
                v___x_6679_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(
                    v_item_6671_,
                    v___x_6678_,
                    v___y_6672_,
                    v___y_6673_,
                    v___y_6674_,
                    v___y_6675_,
                    v___y_6676_,
                    v___y_6677_,
                );
                return v___x_6679_;
            }
            2 => {
                v_proofs_6702_ = lean_ctor_get_uint8(v_config_6661_, 0 as u32);
                v_types_6703_ = lean_ctor_get_uint8(v_config_6661_, 1 as u32);
                v_implicits_6704_ = lean_ctor_get_uint8(v_config_6661_, 2 as u32);
                v_descend_6705_ = lean_ctor_get_uint8(v_config_6661_, 3 as u32);
                v_underBinder_6706_ = lean_ctor_get_uint8(v_config_6661_, 4 as u32);
                v_merge_6707_ = lean_ctor_get_uint8(v_config_6661_, 6 as u32);
                v_useContext_6708_ = lean_ctor_get_uint8(v_config_6661_, 7 as u32);
                v_onlyGivenNames_6709_ = lean_ctor_get_uint8(v_config_6661_, 8 as u32);
                v_preserveBinderNames_6710_ = lean_ctor_get_uint8(v_config_6661_, 9 as u32);
                v_lift_6711_ = lean_ctor_get_uint8(v_config_6661_, 10 as u32);
                v_isSharedCheck_6722_ = (!lean_is_exclusive(v_config_6661_)) as u8;
                if v_isSharedCheck_6722_ == 0 {
                    v___x_6713_ = v_config_6661_;
                    v_isShared_6714_ = v_isSharedCheck_6722_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_config_6661_);
                    v___x_6713_ = lean_box(0);
                    v_isShared_6714_ = v_isSharedCheck_6722_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6714_ == 0 {
                    v___x_6716_ = v___x_6713_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6721_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6721_, 0 as u32, v_proofs_6702_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6721_, 1 as u32, v_types_6703_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6721_, 2 as u32, v_implicits_6704_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6721_, 3 as u32, v_descend_6705_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6721_, 4 as u32, v_underBinder_6706_);
                    v___x_6716_ = v_reuseFailAlloc_6721_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6717_ = (lean_unbox(v_a_6698_) as u8);
                lean_dec(v_a_6698_);
                lean_ctor_set_uint8(v___x_6716_, 5 as u32, v___x_6717_);
                lean_ctor_set_uint8(v___x_6716_, 6 as u32, v_merge_6707_);
                lean_ctor_set_uint8(v___x_6716_, 7 as u32, v_useContext_6708_);
                lean_ctor_set_uint8(v___x_6716_, 8 as u32, v_onlyGivenNames_6709_);
                lean_ctor_set_uint8(v___x_6716_, 9 as u32, v_preserveBinderNames_6710_);
                lean_ctor_set_uint8(v___x_6716_, 10 as u32, v_lift_6711_);
                if v_isShared_6701_ == 0 {
                    lean_ctor_set(v___x_6700_, 0, v___x_6716_);
                    v___x_6719_ = v___x_6700_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6720_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6720_, 0, v___x_6716_);
                    v___x_6719_ = v_reuseFailAlloc_6720_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6719_;
            }
            6 => {
                if v_isShared_6727_ == 0 {
                    v___x_6729_ = v___x_6726_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6730_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6730_, 0, v_a_6724_);
                    v___x_6729_ = v_reuseFailAlloc_6730_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6729_;
            }
            8 => {
                if v_isShared_6735_ == 0 {
                    v___x_6737_ = v___x_6734_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6738_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6738_, 0, v_a_6732_);
                    v___x_6737_ = v_reuseFailAlloc_6738_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6737_;
            }
            10 => {
                v_proofs_6748_ = lean_ctor_get_uint8(v_config_6661_, 0 as u32);
                v_types_6749_ = lean_ctor_get_uint8(v_config_6661_, 1 as u32);
                v_implicits_6750_ = lean_ctor_get_uint8(v_config_6661_, 2 as u32);
                v_descend_6751_ = lean_ctor_get_uint8(v_config_6661_, 3 as u32);
                v_underBinder_6752_ = lean_ctor_get_uint8(v_config_6661_, 4 as u32);
                v_usedOnly_6753_ = lean_ctor_get_uint8(v_config_6661_, 5 as u32);
                v_merge_6754_ = lean_ctor_get_uint8(v_config_6661_, 6 as u32);
                v_onlyGivenNames_6755_ = lean_ctor_get_uint8(v_config_6661_, 8 as u32);
                v_preserveBinderNames_6756_ = lean_ctor_get_uint8(v_config_6661_, 9 as u32);
                v_lift_6757_ = lean_ctor_get_uint8(v_config_6661_, 10 as u32);
                v_isSharedCheck_6768_ = (!lean_is_exclusive(v_config_6661_)) as u8;
                if v_isSharedCheck_6768_ == 0 {
                    v___x_6759_ = v_config_6661_;
                    v_isShared_6760_ = v_isSharedCheck_6768_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_config_6661_);
                    v___x_6759_ = lean_box(0);
                    v_isShared_6760_ = v_isSharedCheck_6768_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_6760_ == 0 {
                    v___x_6762_ = v___x_6759_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6767_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6767_, 0 as u32, v_proofs_6748_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6767_, 1 as u32, v_types_6749_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6767_, 2 as u32, v_implicits_6750_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6767_, 3 as u32, v_descend_6751_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6767_, 4 as u32, v_underBinder_6752_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6767_, 5 as u32, v_usedOnly_6753_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6767_, 6 as u32, v_merge_6754_);
                    v___x_6762_ = v_reuseFailAlloc_6767_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_6763_ = (lean_unbox(v_a_6744_) as u8);
                lean_dec(v_a_6744_);
                lean_ctor_set_uint8(v___x_6762_, 7 as u32, v___x_6763_);
                lean_ctor_set_uint8(v___x_6762_, 8 as u32, v_onlyGivenNames_6755_);
                lean_ctor_set_uint8(v___x_6762_, 9 as u32, v_preserveBinderNames_6756_);
                lean_ctor_set_uint8(v___x_6762_, 10 as u32, v_lift_6757_);
                if v_isShared_6747_ == 0 {
                    lean_ctor_set(v___x_6746_, 0, v___x_6762_);
                    v___x_6765_ = v___x_6746_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6766_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6766_, 0, v___x_6762_);
                    v___x_6765_ = v_reuseFailAlloc_6766_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6765_;
            }
            14 => {
                if v_isShared_6773_ == 0 {
                    v___x_6775_ = v___x_6772_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6776_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6776_, 0, v_a_6770_);
                    v___x_6775_ = v_reuseFailAlloc_6776_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6775_;
            }
            16 => {
                if v_isShared_6781_ == 0 {
                    v___x_6783_ = v___x_6780_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6784_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6784_, 0, v_a_6778_);
                    v___x_6783_ = v_reuseFailAlloc_6784_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6783_;
            }
            18 => {
                v_proofs_6794_ = lean_ctor_get_uint8(v_config_6661_, 0 as u32);
                v_types_6795_ = lean_ctor_get_uint8(v_config_6661_, 1 as u32);
                v_implicits_6796_ = lean_ctor_get_uint8(v_config_6661_, 2 as u32);
                v_descend_6797_ = lean_ctor_get_uint8(v_config_6661_, 3 as u32);
                v_usedOnly_6798_ = lean_ctor_get_uint8(v_config_6661_, 5 as u32);
                v_merge_6799_ = lean_ctor_get_uint8(v_config_6661_, 6 as u32);
                v_useContext_6800_ = lean_ctor_get_uint8(v_config_6661_, 7 as u32);
                v_onlyGivenNames_6801_ = lean_ctor_get_uint8(v_config_6661_, 8 as u32);
                v_preserveBinderNames_6802_ = lean_ctor_get_uint8(v_config_6661_, 9 as u32);
                v_lift_6803_ = lean_ctor_get_uint8(v_config_6661_, 10 as u32);
                v_isSharedCheck_6814_ = (!lean_is_exclusive(v_config_6661_)) as u8;
                if v_isSharedCheck_6814_ == 0 {
                    v___x_6805_ = v_config_6661_;
                    v_isShared_6806_ = v_isSharedCheck_6814_;
                    state = 19;
                    continue;
                } else {
                    lean_dec(v_config_6661_);
                    v___x_6805_ = lean_box(0);
                    v_isShared_6806_ = v_isSharedCheck_6814_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_6806_ == 0 {
                    v___x_6808_ = v___x_6805_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6813_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6813_, 0 as u32, v_proofs_6794_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6813_, 1 as u32, v_types_6795_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6813_, 2 as u32, v_implicits_6796_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6813_, 3 as u32, v_descend_6797_);
                    v___x_6808_ = v_reuseFailAlloc_6813_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_6809_ = (lean_unbox(v_a_6790_) as u8);
                lean_dec(v_a_6790_);
                lean_ctor_set_uint8(v___x_6808_, 4 as u32, v___x_6809_);
                lean_ctor_set_uint8(v___x_6808_, 5 as u32, v_usedOnly_6798_);
                lean_ctor_set_uint8(v___x_6808_, 6 as u32, v_merge_6799_);
                lean_ctor_set_uint8(v___x_6808_, 7 as u32, v_useContext_6800_);
                lean_ctor_set_uint8(v___x_6808_, 8 as u32, v_onlyGivenNames_6801_);
                lean_ctor_set_uint8(v___x_6808_, 9 as u32, v_preserveBinderNames_6802_);
                lean_ctor_set_uint8(v___x_6808_, 10 as u32, v_lift_6803_);
                if v_isShared_6793_ == 0 {
                    lean_ctor_set(v___x_6792_, 0, v___x_6808_);
                    v___x_6811_ = v___x_6792_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6812_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6812_, 0, v___x_6808_);
                    v___x_6811_ = v_reuseFailAlloc_6812_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6811_;
            }
            22 => {
                if v_isShared_6819_ == 0 {
                    v___x_6821_ = v___x_6818_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6822_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6822_, 0, v_a_6816_);
                    v___x_6821_ = v_reuseFailAlloc_6822_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6821_;
            }
            24 => {
                if v_isShared_6827_ == 0 {
                    v___x_6829_ = v___x_6826_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6830_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6830_, 0, v_a_6824_);
                    v___x_6829_ = v_reuseFailAlloc_6830_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6829_;
            }
            26 => {
                v_proofs_6845_ = lean_ctor_get_uint8(v_config_6661_, 0 as u32);
                v_implicits_6846_ = lean_ctor_get_uint8(v_config_6661_, 2 as u32);
                v_descend_6847_ = lean_ctor_get_uint8(v_config_6661_, 3 as u32);
                v_underBinder_6848_ = lean_ctor_get_uint8(v_config_6661_, 4 as u32);
                v_usedOnly_6849_ = lean_ctor_get_uint8(v_config_6661_, 5 as u32);
                v_merge_6850_ = lean_ctor_get_uint8(v_config_6661_, 6 as u32);
                v_useContext_6851_ = lean_ctor_get_uint8(v_config_6661_, 7 as u32);
                v_onlyGivenNames_6852_ = lean_ctor_get_uint8(v_config_6661_, 8 as u32);
                v_preserveBinderNames_6853_ = lean_ctor_get_uint8(v_config_6661_, 9 as u32);
                v_lift_6854_ = lean_ctor_get_uint8(v_config_6661_, 10 as u32);
                v_isSharedCheck_6865_ = (!lean_is_exclusive(v_config_6661_)) as u8;
                if v_isSharedCheck_6865_ == 0 {
                    v___x_6856_ = v_config_6661_;
                    v_isShared_6857_ = v_isSharedCheck_6865_;
                    state = 27;
                    continue;
                } else {
                    lean_dec(v_config_6661_);
                    v___x_6856_ = lean_box(0);
                    v_isShared_6857_ = v_isSharedCheck_6865_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_6857_ == 0 {
                    v___x_6859_ = v___x_6856_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6864_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6864_, 0 as u32, v_proofs_6845_);
                    v___x_6859_ = v_reuseFailAlloc_6864_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_6860_ = (lean_unbox(v_a_6841_) as u8);
                lean_dec(v_a_6841_);
                lean_ctor_set_uint8(v___x_6859_, 1 as u32, v___x_6860_);
                lean_ctor_set_uint8(v___x_6859_, 2 as u32, v_implicits_6846_);
                lean_ctor_set_uint8(v___x_6859_, 3 as u32, v_descend_6847_);
                lean_ctor_set_uint8(v___x_6859_, 4 as u32, v_underBinder_6848_);
                lean_ctor_set_uint8(v___x_6859_, 5 as u32, v_usedOnly_6849_);
                lean_ctor_set_uint8(v___x_6859_, 6 as u32, v_merge_6850_);
                lean_ctor_set_uint8(v___x_6859_, 7 as u32, v_useContext_6851_);
                lean_ctor_set_uint8(v___x_6859_, 8 as u32, v_onlyGivenNames_6852_);
                lean_ctor_set_uint8(v___x_6859_, 9 as u32, v_preserveBinderNames_6853_);
                lean_ctor_set_uint8(v___x_6859_, 10 as u32, v_lift_6854_);
                if v_isShared_6844_ == 0 {
                    lean_ctor_set(v___x_6843_, 0, v___x_6859_);
                    v___x_6862_ = v___x_6843_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6863_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6863_, 0, v___x_6859_);
                    v___x_6862_ = v_reuseFailAlloc_6863_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_6862_;
            }
            30 => {
                if v_isShared_6870_ == 0 {
                    v___x_6872_ = v___x_6869_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_6873_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6873_, 0, v_a_6867_);
                    v___x_6872_ = v_reuseFailAlloc_6873_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_6872_;
            }
            32 => {
                if v_isShared_6878_ == 0 {
                    v___x_6880_ = v___x_6877_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6881_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6881_, 0, v_a_6875_);
                    v___x_6880_ = v_reuseFailAlloc_6881_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_6880_;
            }
            34 => {
                v_types_6891_ = lean_ctor_get_uint8(v_config_6661_, 1 as u32);
                v_implicits_6892_ = lean_ctor_get_uint8(v_config_6661_, 2 as u32);
                v_descend_6893_ = lean_ctor_get_uint8(v_config_6661_, 3 as u32);
                v_underBinder_6894_ = lean_ctor_get_uint8(v_config_6661_, 4 as u32);
                v_usedOnly_6895_ = lean_ctor_get_uint8(v_config_6661_, 5 as u32);
                v_merge_6896_ = lean_ctor_get_uint8(v_config_6661_, 6 as u32);
                v_useContext_6897_ = lean_ctor_get_uint8(v_config_6661_, 7 as u32);
                v_onlyGivenNames_6898_ = lean_ctor_get_uint8(v_config_6661_, 8 as u32);
                v_preserveBinderNames_6899_ = lean_ctor_get_uint8(v_config_6661_, 9 as u32);
                v_lift_6900_ = lean_ctor_get_uint8(v_config_6661_, 10 as u32);
                v_isSharedCheck_6911_ = (!lean_is_exclusive(v_config_6661_)) as u8;
                if v_isSharedCheck_6911_ == 0 {
                    v___x_6902_ = v_config_6661_;
                    v_isShared_6903_ = v_isSharedCheck_6911_;
                    state = 35;
                    continue;
                } else {
                    lean_dec(v_config_6661_);
                    v___x_6902_ = lean_box(0);
                    v_isShared_6903_ = v_isSharedCheck_6911_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_6903_ == 0 {
                    v___x_6905_ = v___x_6902_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_6910_ = lean_alloc_ctor(0, 0, (11) as u32);
                    v___x_6905_ = v_reuseFailAlloc_6910_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                v___x_6906_ = (lean_unbox(v_a_6887_) as u8);
                lean_dec(v_a_6887_);
                lean_ctor_set_uint8(v___x_6905_, 0 as u32, v___x_6906_);
                lean_ctor_set_uint8(v___x_6905_, 1 as u32, v_types_6891_);
                lean_ctor_set_uint8(v___x_6905_, 2 as u32, v_implicits_6892_);
                lean_ctor_set_uint8(v___x_6905_, 3 as u32, v_descend_6893_);
                lean_ctor_set_uint8(v___x_6905_, 4 as u32, v_underBinder_6894_);
                lean_ctor_set_uint8(v___x_6905_, 5 as u32, v_usedOnly_6895_);
                lean_ctor_set_uint8(v___x_6905_, 6 as u32, v_merge_6896_);
                lean_ctor_set_uint8(v___x_6905_, 7 as u32, v_useContext_6897_);
                lean_ctor_set_uint8(v___x_6905_, 8 as u32, v_onlyGivenNames_6898_);
                lean_ctor_set_uint8(v___x_6905_, 9 as u32, v_preserveBinderNames_6899_);
                lean_ctor_set_uint8(v___x_6905_, 10 as u32, v_lift_6900_);
                if v_isShared_6890_ == 0 {
                    lean_ctor_set(v___x_6889_, 0, v___x_6905_);
                    v___x_6908_ = v___x_6889_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_6909_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6909_, 0, v___x_6905_);
                    v___x_6908_ = v_reuseFailAlloc_6909_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_6908_;
            }
            38 => {
                if v_isShared_6916_ == 0 {
                    v___x_6918_ = v___x_6915_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_6919_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6919_, 0, v_a_6913_);
                    v___x_6918_ = v_reuseFailAlloc_6919_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_6918_;
            }
            40 => {
                if v_isShared_6924_ == 0 {
                    v___x_6926_ = v___x_6923_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_6927_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6927_, 0, v_a_6921_);
                    v___x_6926_ = v_reuseFailAlloc_6927_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_6926_;
            }
            42 => {
                v_proofs_6937_ = lean_ctor_get_uint8(v_config_6661_, 0 as u32);
                v_types_6938_ = lean_ctor_get_uint8(v_config_6661_, 1 as u32);
                v_implicits_6939_ = lean_ctor_get_uint8(v_config_6661_, 2 as u32);
                v_descend_6940_ = lean_ctor_get_uint8(v_config_6661_, 3 as u32);
                v_underBinder_6941_ = lean_ctor_get_uint8(v_config_6661_, 4 as u32);
                v_usedOnly_6942_ = lean_ctor_get_uint8(v_config_6661_, 5 as u32);
                v_merge_6943_ = lean_ctor_get_uint8(v_config_6661_, 6 as u32);
                v_useContext_6944_ = lean_ctor_get_uint8(v_config_6661_, 7 as u32);
                v_onlyGivenNames_6945_ = lean_ctor_get_uint8(v_config_6661_, 8 as u32);
                v_lift_6946_ = lean_ctor_get_uint8(v_config_6661_, 10 as u32);
                v_isSharedCheck_6957_ = (!lean_is_exclusive(v_config_6661_)) as u8;
                if v_isSharedCheck_6957_ == 0 {
                    v___x_6948_ = v_config_6661_;
                    v_isShared_6949_ = v_isSharedCheck_6957_;
                    state = 43;
                    continue;
                } else {
                    lean_dec(v_config_6661_);
                    v___x_6948_ = lean_box(0);
                    v_isShared_6949_ = v_isSharedCheck_6957_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_6949_ == 0 {
                    v___x_6951_ = v___x_6948_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_6956_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6956_, 0 as u32, v_proofs_6937_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6956_, 1 as u32, v_types_6938_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6956_, 2 as u32, v_implicits_6939_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6956_, 3 as u32, v_descend_6940_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6956_, 4 as u32, v_underBinder_6941_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6956_, 5 as u32, v_usedOnly_6942_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6956_, 6 as u32, v_merge_6943_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6956_, 7 as u32, v_useContext_6944_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6956_, 8 as u32, v_onlyGivenNames_6945_);
                    v___x_6951_ = v_reuseFailAlloc_6956_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_6952_ = (lean_unbox(v_a_6933_) as u8);
                lean_dec(v_a_6933_);
                lean_ctor_set_uint8(v___x_6951_, 9 as u32, v___x_6952_);
                lean_ctor_set_uint8(v___x_6951_, 10 as u32, v_lift_6946_);
                if v_isShared_6936_ == 0 {
                    lean_ctor_set(v___x_6935_, 0, v___x_6951_);
                    v___x_6954_ = v___x_6935_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_6955_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6955_, 0, v___x_6951_);
                    v___x_6954_ = v_reuseFailAlloc_6955_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_6954_;
            }
            46 => {
                if v_isShared_6962_ == 0 {
                    v___x_6964_ = v___x_6961_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_6965_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6965_, 0, v_a_6959_);
                    v___x_6964_ = v_reuseFailAlloc_6965_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_6964_;
            }
            48 => {
                if v_isShared_6970_ == 0 {
                    v___x_6972_ = v___x_6969_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_6973_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6973_, 0, v_a_6967_);
                    v___x_6972_ = v_reuseFailAlloc_6973_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_6972_;
            }
            50 => {
                v_proofs_6990_ = lean_ctor_get_uint8(v_config_6661_, 0 as u32);
                v_types_6991_ = lean_ctor_get_uint8(v_config_6661_, 1 as u32);
                v_implicits_6992_ = lean_ctor_get_uint8(v_config_6661_, 2 as u32);
                v_descend_6993_ = lean_ctor_get_uint8(v_config_6661_, 3 as u32);
                v_underBinder_6994_ = lean_ctor_get_uint8(v_config_6661_, 4 as u32);
                v_usedOnly_6995_ = lean_ctor_get_uint8(v_config_6661_, 5 as u32);
                v_merge_6996_ = lean_ctor_get_uint8(v_config_6661_, 6 as u32);
                v_useContext_6997_ = lean_ctor_get_uint8(v_config_6661_, 7 as u32);
                v_preserveBinderNames_6998_ = lean_ctor_get_uint8(v_config_6661_, 9 as u32);
                v_lift_6999_ = lean_ctor_get_uint8(v_config_6661_, 10 as u32);
                v_isSharedCheck_7010_ = (!lean_is_exclusive(v_config_6661_)) as u8;
                if v_isSharedCheck_7010_ == 0 {
                    v___x_7001_ = v_config_6661_;
                    v_isShared_7002_ = v_isSharedCheck_7010_;
                    state = 51;
                    continue;
                } else {
                    lean_dec(v_config_6661_);
                    v___x_7001_ = lean_box(0);
                    v_isShared_7002_ = v_isSharedCheck_7010_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                if v_isShared_7002_ == 0 {
                    v___x_7004_ = v___x_7001_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_7009_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7009_, 0 as u32, v_proofs_6990_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7009_, 1 as u32, v_types_6991_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7009_, 2 as u32, v_implicits_6992_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7009_, 3 as u32, v_descend_6993_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7009_, 4 as u32, v_underBinder_6994_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7009_, 5 as u32, v_usedOnly_6995_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7009_, 6 as u32, v_merge_6996_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7009_, 7 as u32, v_useContext_6997_);
                    v___x_7004_ = v_reuseFailAlloc_7009_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                v___x_7005_ = (lean_unbox(v_a_6986_) as u8);
                lean_dec(v_a_6986_);
                lean_ctor_set_uint8(v___x_7004_, 8 as u32, v___x_7005_);
                lean_ctor_set_uint8(v___x_7004_, 9 as u32, v_preserveBinderNames_6998_);
                lean_ctor_set_uint8(v___x_7004_, 10 as u32, v_lift_6999_);
                if v_isShared_6989_ == 0 {
                    lean_ctor_set(v___x_6988_, 0, v___x_7004_);
                    v___x_7007_ = v___x_6988_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_7008_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7008_, 0, v___x_7004_);
                    v___x_7007_ = v_reuseFailAlloc_7008_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_7007_;
            }
            54 => {
                if v_isShared_7015_ == 0 {
                    v___x_7017_ = v___x_7014_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_7018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7018_, 0, v_a_7012_);
                    v___x_7017_ = v_reuseFailAlloc_7018_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_7017_;
            }
            56 => {
                if v_isShared_7023_ == 0 {
                    v___x_7025_ = v___x_7022_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_7026_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7026_, 0, v_a_7020_);
                    v___x_7025_ = v_reuseFailAlloc_7026_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_7025_;
            }
            58 => {
                v_proofs_7036_ = lean_ctor_get_uint8(v_config_6661_, 0 as u32);
                v_types_7037_ = lean_ctor_get_uint8(v_config_6661_, 1 as u32);
                v_implicits_7038_ = lean_ctor_get_uint8(v_config_6661_, 2 as u32);
                v_descend_7039_ = lean_ctor_get_uint8(v_config_6661_, 3 as u32);
                v_underBinder_7040_ = lean_ctor_get_uint8(v_config_6661_, 4 as u32);
                v_usedOnly_7041_ = lean_ctor_get_uint8(v_config_6661_, 5 as u32);
                v_useContext_7042_ = lean_ctor_get_uint8(v_config_6661_, 7 as u32);
                v_onlyGivenNames_7043_ = lean_ctor_get_uint8(v_config_6661_, 8 as u32);
                v_preserveBinderNames_7044_ = lean_ctor_get_uint8(v_config_6661_, 9 as u32);
                v_lift_7045_ = lean_ctor_get_uint8(v_config_6661_, 10 as u32);
                v_isSharedCheck_7056_ = (!lean_is_exclusive(v_config_6661_)) as u8;
                if v_isSharedCheck_7056_ == 0 {
                    v___x_7047_ = v_config_6661_;
                    v_isShared_7048_ = v_isSharedCheck_7056_;
                    state = 59;
                    continue;
                } else {
                    lean_dec(v_config_6661_);
                    v___x_7047_ = lean_box(0);
                    v_isShared_7048_ = v_isSharedCheck_7056_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                if v_isShared_7048_ == 0 {
                    v___x_7050_ = v___x_7047_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_7055_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7055_, 0 as u32, v_proofs_7036_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7055_, 1 as u32, v_types_7037_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7055_, 2 as u32, v_implicits_7038_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7055_, 3 as u32, v_descend_7039_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7055_, 4 as u32, v_underBinder_7040_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7055_, 5 as u32, v_usedOnly_7041_);
                    v___x_7050_ = v_reuseFailAlloc_7055_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_7051_ = (lean_unbox(v_a_7032_) as u8);
                lean_dec(v_a_7032_);
                lean_ctor_set_uint8(v___x_7050_, 6 as u32, v___x_7051_);
                lean_ctor_set_uint8(v___x_7050_, 7 as u32, v_useContext_7042_);
                lean_ctor_set_uint8(v___x_7050_, 8 as u32, v_onlyGivenNames_7043_);
                lean_ctor_set_uint8(v___x_7050_, 9 as u32, v_preserveBinderNames_7044_);
                lean_ctor_set_uint8(v___x_7050_, 10 as u32, v_lift_7045_);
                if v_isShared_7035_ == 0 {
                    lean_ctor_set(v___x_7034_, 0, v___x_7050_);
                    v___x_7053_ = v___x_7034_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_7054_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7054_, 0, v___x_7050_);
                    v___x_7053_ = v_reuseFailAlloc_7054_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_7053_;
            }
            62 => {
                if v_isShared_7061_ == 0 {
                    v___x_7063_ = v___x_7060_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_7064_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7064_, 0, v_a_7058_);
                    v___x_7063_ = v_reuseFailAlloc_7064_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_7063_;
            }
            64 => {
                if v_isShared_7069_ == 0 {
                    v___x_7071_ = v___x_7068_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_7072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7072_, 0, v_a_7066_);
                    v___x_7071_ = v_reuseFailAlloc_7072_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_7071_;
            }
            66 => {
                v_proofs_7082_ = lean_ctor_get_uint8(v_config_6661_, 0 as u32);
                v_types_7083_ = lean_ctor_get_uint8(v_config_6661_, 1 as u32);
                v_implicits_7084_ = lean_ctor_get_uint8(v_config_6661_, 2 as u32);
                v_descend_7085_ = lean_ctor_get_uint8(v_config_6661_, 3 as u32);
                v_underBinder_7086_ = lean_ctor_get_uint8(v_config_6661_, 4 as u32);
                v_usedOnly_7087_ = lean_ctor_get_uint8(v_config_6661_, 5 as u32);
                v_merge_7088_ = lean_ctor_get_uint8(v_config_6661_, 6 as u32);
                v_useContext_7089_ = lean_ctor_get_uint8(v_config_6661_, 7 as u32);
                v_onlyGivenNames_7090_ = lean_ctor_get_uint8(v_config_6661_, 8 as u32);
                v_preserveBinderNames_7091_ = lean_ctor_get_uint8(v_config_6661_, 9 as u32);
                v_isSharedCheck_7102_ = (!lean_is_exclusive(v_config_6661_)) as u8;
                if v_isSharedCheck_7102_ == 0 {
                    v___x_7093_ = v_config_6661_;
                    v_isShared_7094_ = v_isSharedCheck_7102_;
                    state = 67;
                    continue;
                } else {
                    lean_dec(v_config_6661_);
                    v___x_7093_ = lean_box(0);
                    v_isShared_7094_ = v_isSharedCheck_7102_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                if v_isShared_7094_ == 0 {
                    v___x_7096_ = v___x_7093_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_7101_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7101_, 0 as u32, v_proofs_7082_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7101_, 1 as u32, v_types_7083_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7101_, 2 as u32, v_implicits_7084_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7101_, 3 as u32, v_descend_7085_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7101_, 4 as u32, v_underBinder_7086_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7101_, 5 as u32, v_usedOnly_7087_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7101_, 6 as u32, v_merge_7088_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7101_, 7 as u32, v_useContext_7089_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7101_, 8 as u32, v_onlyGivenNames_7090_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7101_,
                        9 as u32,
                        v_preserveBinderNames_7091_,
                    );
                    v___x_7096_ = v_reuseFailAlloc_7101_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                v___x_7097_ = (lean_unbox(v_a_7078_) as u8);
                lean_dec(v_a_7078_);
                lean_ctor_set_uint8(v___x_7096_, 10 as u32, v___x_7097_);
                if v_isShared_7081_ == 0 {
                    lean_ctor_set(v___x_7080_, 0, v___x_7096_);
                    v___x_7099_ = v___x_7080_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_7100_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7100_, 0, v___x_7096_);
                    v___x_7099_ = v_reuseFailAlloc_7100_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                return v___x_7099_;
            }
            70 => {
                if v_isShared_7107_ == 0 {
                    v___x_7109_ = v___x_7106_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_7110_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7110_, 0, v_a_7104_);
                    v___x_7109_ = v_reuseFailAlloc_7110_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                return v___x_7109_;
            }
            72 => {
                if v_isShared_7115_ == 0 {
                    v___x_7117_ = v___x_7114_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_7118_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7118_, 0, v_a_7112_);
                    v___x_7117_ = v_reuseFailAlloc_7118_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                return v___x_7117_;
            }
            74 => {
                v_proofs_7134_ = lean_ctor_get_uint8(v_config_6661_, 0 as u32);
                v_types_7135_ = lean_ctor_get_uint8(v_config_6661_, 1 as u32);
                v_descend_7136_ = lean_ctor_get_uint8(v_config_6661_, 3 as u32);
                v_underBinder_7137_ = lean_ctor_get_uint8(v_config_6661_, 4 as u32);
                v_usedOnly_7138_ = lean_ctor_get_uint8(v_config_6661_, 5 as u32);
                v_merge_7139_ = lean_ctor_get_uint8(v_config_6661_, 6 as u32);
                v_useContext_7140_ = lean_ctor_get_uint8(v_config_6661_, 7 as u32);
                v_onlyGivenNames_7141_ = lean_ctor_get_uint8(v_config_6661_, 8 as u32);
                v_preserveBinderNames_7142_ = lean_ctor_get_uint8(v_config_6661_, 9 as u32);
                v_lift_7143_ = lean_ctor_get_uint8(v_config_6661_, 10 as u32);
                v_isSharedCheck_7154_ = (!lean_is_exclusive(v_config_6661_)) as u8;
                if v_isSharedCheck_7154_ == 0 {
                    v___x_7145_ = v_config_6661_;
                    v_isShared_7146_ = v_isSharedCheck_7154_;
                    state = 75;
                    continue;
                } else {
                    lean_dec(v_config_6661_);
                    v___x_7145_ = lean_box(0);
                    v_isShared_7146_ = v_isSharedCheck_7154_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                if v_isShared_7146_ == 0 {
                    v___x_7148_ = v___x_7145_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_7153_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7153_, 0 as u32, v_proofs_7134_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7153_, 1 as u32, v_types_7135_);
                    v___x_7148_ = v_reuseFailAlloc_7153_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                v___x_7149_ = (lean_unbox(v_a_7130_) as u8);
                lean_dec(v_a_7130_);
                lean_ctor_set_uint8(v___x_7148_, 2 as u32, v___x_7149_);
                lean_ctor_set_uint8(v___x_7148_, 3 as u32, v_descend_7136_);
                lean_ctor_set_uint8(v___x_7148_, 4 as u32, v_underBinder_7137_);
                lean_ctor_set_uint8(v___x_7148_, 5 as u32, v_usedOnly_7138_);
                lean_ctor_set_uint8(v___x_7148_, 6 as u32, v_merge_7139_);
                lean_ctor_set_uint8(v___x_7148_, 7 as u32, v_useContext_7140_);
                lean_ctor_set_uint8(v___x_7148_, 8 as u32, v_onlyGivenNames_7141_);
                lean_ctor_set_uint8(v___x_7148_, 9 as u32, v_preserveBinderNames_7142_);
                lean_ctor_set_uint8(v___x_7148_, 10 as u32, v_lift_7143_);
                if v_isShared_7133_ == 0 {
                    lean_ctor_set(v___x_7132_, 0, v___x_7148_);
                    v___x_7151_ = v___x_7132_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_7152_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7152_, 0, v___x_7148_);
                    v___x_7151_ = v_reuseFailAlloc_7152_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                return v___x_7151_;
            }
            78 => {
                if v_isShared_7159_ == 0 {
                    v___x_7161_ = v___x_7158_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_7162_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7162_, 0, v_a_7156_);
                    v___x_7161_ = v_reuseFailAlloc_7162_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_7161_;
            }
            80 => {
                if v_isShared_7167_ == 0 {
                    v___x_7169_ = v___x_7166_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_7170_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7170_, 0, v_a_7164_);
                    v___x_7169_ = v_reuseFailAlloc_7170_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                return v___x_7169_;
            }
            82 => {
                v_proofs_7180_ = lean_ctor_get_uint8(v_config_6661_, 0 as u32);
                v_types_7181_ = lean_ctor_get_uint8(v_config_6661_, 1 as u32);
                v_implicits_7182_ = lean_ctor_get_uint8(v_config_6661_, 2 as u32);
                v_underBinder_7183_ = lean_ctor_get_uint8(v_config_6661_, 4 as u32);
                v_usedOnly_7184_ = lean_ctor_get_uint8(v_config_6661_, 5 as u32);
                v_merge_7185_ = lean_ctor_get_uint8(v_config_6661_, 6 as u32);
                v_useContext_7186_ = lean_ctor_get_uint8(v_config_6661_, 7 as u32);
                v_onlyGivenNames_7187_ = lean_ctor_get_uint8(v_config_6661_, 8 as u32);
                v_preserveBinderNames_7188_ = lean_ctor_get_uint8(v_config_6661_, 9 as u32);
                v_lift_7189_ = lean_ctor_get_uint8(v_config_6661_, 10 as u32);
                v_isSharedCheck_7200_ = (!lean_is_exclusive(v_config_6661_)) as u8;
                if v_isSharedCheck_7200_ == 0 {
                    v___x_7191_ = v_config_6661_;
                    v_isShared_7192_ = v_isSharedCheck_7200_;
                    state = 83;
                    continue;
                } else {
                    lean_dec(v_config_6661_);
                    v___x_7191_ = lean_box(0);
                    v_isShared_7192_ = v_isSharedCheck_7200_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_7192_ == 0 {
                    v___x_7194_ = v___x_7191_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_7199_ = lean_alloc_ctor(0, 0, (11) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7199_, 0 as u32, v_proofs_7180_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7199_, 1 as u32, v_types_7181_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7199_, 2 as u32, v_implicits_7182_);
                    v___x_7194_ = v_reuseFailAlloc_7199_;
                    state = 84;
                    continue;
                }
            }
            84 => {
                v___x_7195_ = (lean_unbox(v_a_7176_) as u8);
                lean_dec(v_a_7176_);
                lean_ctor_set_uint8(v___x_7194_, 3 as u32, v___x_7195_);
                lean_ctor_set_uint8(v___x_7194_, 4 as u32, v_underBinder_7183_);
                lean_ctor_set_uint8(v___x_7194_, 5 as u32, v_usedOnly_7184_);
                lean_ctor_set_uint8(v___x_7194_, 6 as u32, v_merge_7185_);
                lean_ctor_set_uint8(v___x_7194_, 7 as u32, v_useContext_7186_);
                lean_ctor_set_uint8(v___x_7194_, 8 as u32, v_onlyGivenNames_7187_);
                lean_ctor_set_uint8(v___x_7194_, 9 as u32, v_preserveBinderNames_7188_);
                lean_ctor_set_uint8(v___x_7194_, 10 as u32, v_lift_7189_);
                if v_isShared_7179_ == 0 {
                    lean_ctor_set(v___x_7178_, 0, v___x_7194_);
                    v___x_7197_ = v___x_7178_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_7198_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7198_, 0, v___x_7194_);
                    v___x_7197_ = v_reuseFailAlloc_7198_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                return v___x_7197_;
            }
            86 => {
                if v_isShared_7205_ == 0 {
                    v___x_7207_ = v___x_7204_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_7208_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7208_, 0, v_a_7202_);
                    v___x_7207_ = v_reuseFailAlloc_7208_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                return v___x_7207_;
            }
            88 => {
                if v_isShared_7213_ == 0 {
                    v___x_7215_ = v___x_7212_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_7216_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7216_, 0, v_a_7210_);
                    v___x_7215_ = v_reuseFailAlloc_7216_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                return v___x_7215_;
            }
            90 => {
                if v_isShared_7224_ == 0 {
                    v___x_7226_ = v___x_7223_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_7227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7227_, 0, v_a_7221_);
                    v___x_7226_ = v_reuseFailAlloc_7227_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_7226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0___boxed(
    mut v_config_7229_: *mut LeanObject,
    mut v_item_7230_: *mut LeanObject,
    mut v___y_7231_: *mut LeanObject,
    mut v___y_7232_: *mut LeanObject,
    mut v___y_7233_: *mut LeanObject,
    mut v___y_7234_: *mut LeanObject,
    mut v___y_7235_: *mut LeanObject,
    mut v___y_7236_: *mut LeanObject,
    mut v___y_7237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7238_: *mut LeanObject = core::ptr::null_mut();
    v_res_7238_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___lam__0(v_config_7229_, v_item_7230_, v___y_7231_, v___y_7232_, v___y_7233_, v___y_7234_, v___y_7235_, v___y_7236_);
    lean_dec(v___y_7236_);
    lean_dec_ref(v___y_7235_);
    lean_dec(v___y_7234_);
    lean_dec_ref(v___y_7233_);
    lean_dec(v___y_7232_);
    lean_dec_ref(v___y_7231_);
    return v_res_7238_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut LeanObject = core::ptr::null_mut();
    v___x_7241_ = lean_box(0);
    v___x_7242_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig_evalExpr___closed__2;
    v___x_7243_ = l_Lean_mkConst(v___x_7242_, v___x_7241_);
    return v___x_7243_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut LeanObject = core::ptr::null_mut();
    v___x_7244_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__0,
    );
    v___x_7245_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7245_, 0, v___x_7244_);
    return v___x_7245_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0(
    mut v_cfg_7246_: *mut LeanObject,
    mut v_cfgItem_7247_: *mut LeanObject,
    mut v___y_7248_: *mut LeanObject,
    mut v___y_7249_: *mut LeanObject,
    mut v___y_7250_: *mut LeanObject,
    mut v___y_7251_: *mut LeanObject,
    mut v___y_7252_: *mut LeanObject,
    mut v___y_7253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7256_: *mut LeanObject = core::ptr::null_mut();
    v___x_7255_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___closed__1,
    );
    v___x_7256_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(
        v_cfg_7246_,
        v_cfgItem_7247_,
        v___x_7255_,
        v___y_7248_,
        v___y_7249_,
        v___y_7250_,
        v___y_7251_,
        v___y_7252_,
        v___y_7253_,
    );
    return v___x_7256_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0___boxed(
    mut v_cfg_7257_: *mut LeanObject,
    mut v_cfgItem_7258_: *mut LeanObject,
    mut v___y_7259_: *mut LeanObject,
    mut v___y_7260_: *mut LeanObject,
    mut v___y_7261_: *mut LeanObject,
    mut v___y_7262_: *mut LeanObject,
    mut v___y_7263_: *mut LeanObject,
    mut v___y_7264_: *mut LeanObject,
    mut v___y_7265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7266_: *mut LeanObject = core::ptr::null_mut();
    v_res_7266_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___lam__0(
        v_cfg_7257_,
        v_cfgItem_7258_,
        v___y_7259_,
        v___y_7260_,
        v___y_7261_,
        v___y_7262_,
        v___y_7263_,
        v___y_7264_,
    );
    lean_dec(v___y_7264_);
    lean_dec_ref(v___y_7263_);
    lean_dec(v___y_7262_);
    lean_dec_ref(v___y_7261_);
    lean_dec(v___y_7260_);
    lean_dec_ref(v___y_7259_);
    lean_dec(v_cfgItem_7258_);
    return v_res_7266_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(
    mut v_cfg_7268_: *mut LeanObject,
    mut v_init_7269_: *mut LeanObject,
    mut v_logExceptions_7270_: u8,
    mut v_a_7271_: *mut LeanObject,
    mut v_a_7272_: *mut LeanObject,
    mut v_a_7273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_onErr_7275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eval_7276_: *mut LeanObject = core::ptr::null_mut();
    v_onErr_7275_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0;
    v_eval_7276_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_elabLiftLetsConfig_evalConfigItem___closed__0;
    if v_logExceptions_7270_ == 0 {
        let mut v___x_7277_: *mut LeanObject = core::ptr::null_mut();
        v___x_7277_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
            v_eval_7276_,
            v_init_7269_,
            v_cfg_7268_,
            v_onErr_7275_,
            v_logExceptions_7270_,
            v_a_7272_,
            v_a_7273_,
        );
        return v___x_7277_;
    } else {
        let mut v_recover_7278_: u8 = 0;
        let mut v___x_7279_: *mut LeanObject = core::ptr::null_mut();
        v_recover_7278_ = lean_ctor_get_uint8(
            v_a_7271_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        );
        v___x_7279_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
            v_eval_7276_,
            v_init_7269_,
            v_cfg_7268_,
            v_onErr_7275_,
            v_recover_7278_,
            v_a_7272_,
            v_a_7273_,
        );
        return v___x_7279_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___boxed(
    mut v_cfg_7280_: *mut LeanObject,
    mut v_init_7281_: *mut LeanObject,
    mut v_logExceptions_7282_: *mut LeanObject,
    mut v_a_7283_: *mut LeanObject,
    mut v_a_7284_: *mut LeanObject,
    mut v_a_7285_: *mut LeanObject,
    mut v_a_7286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7287_: u8 = 0;
    let mut v_res_7288_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7287_ = (lean_unbox(v_logExceptions_7282_) as u8);
    v_res_7288_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(
        v_cfg_7280_,
        v_init_7281_,
        v_logExceptions_boxed_7287_,
        v_a_7283_,
        v_a_7284_,
        v_a_7285_,
    );
    lean_dec(v_a_7285_);
    lean_dec_ref(v_a_7284_);
    lean_dec_ref(v_a_7283_);
    return v_res_7288_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabLiftLetsConfig(
    mut v_cfg_7289_: *mut LeanObject,
    mut v_init_7290_: *mut LeanObject,
    mut v_logExceptions_7291_: u8,
    mut v_a_7292_: *mut LeanObject,
    mut v_a_7293_: *mut LeanObject,
    mut v_a_7294_: *mut LeanObject,
    mut v_a_7295_: *mut LeanObject,
    mut v_a_7296_: *mut LeanObject,
    mut v_a_7297_: *mut LeanObject,
    mut v_a_7298_: *mut LeanObject,
    mut v_a_7299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7301_: *mut LeanObject = core::ptr::null_mut();
    v___x_7301_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(
        v_cfg_7289_,
        v_init_7290_,
        v_logExceptions_7291_,
        v_a_7292_,
        v_a_7298_,
        v_a_7299_,
    );
    return v___x_7301_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabLiftLetsConfig___boxed(
    mut v_cfg_7302_: *mut LeanObject,
    mut v_init_7303_: *mut LeanObject,
    mut v_logExceptions_7304_: *mut LeanObject,
    mut v_a_7305_: *mut LeanObject,
    mut v_a_7306_: *mut LeanObject,
    mut v_a_7307_: *mut LeanObject,
    mut v_a_7308_: *mut LeanObject,
    mut v_a_7309_: *mut LeanObject,
    mut v_a_7310_: *mut LeanObject,
    mut v_a_7311_: *mut LeanObject,
    mut v_a_7312_: *mut LeanObject,
    mut v_a_7313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7314_: u8 = 0;
    let mut v_res_7315_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7314_ = (lean_unbox(v_logExceptions_7304_) as u8);
    v_res_7315_ = l_Lean_Elab_Tactic_elabLiftLetsConfig(
        v_cfg_7302_,
        v_init_7303_,
        v_logExceptions_boxed_7314_,
        v_a_7305_,
        v_a_7306_,
        v_a_7307_,
        v_a_7308_,
        v_a_7309_,
        v_a_7310_,
        v_a_7311_,
        v_a_7312_,
    );
    lean_dec(v_a_7312_);
    lean_dec_ref(v_a_7311_);
    lean_dec(v_a_7310_);
    lean_dec_ref(v_a_7309_);
    lean_dec(v_a_7308_);
    lean_dec_ref(v_a_7307_);
    lean_dec(v_a_7306_);
    lean_dec_ref(v_a_7305_);
    return v_res_7315_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_7317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut LeanObject = core::ptr::null_mut();
    v___x_7317_ = l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0;
    v___x_7318_ = l_Lean_stringToMessageData(v___x_7317_);
    return v___x_7318_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLiftLets___lam__0(
    mut v_x_7319_: *mut LeanObject,
    mut v___y_7320_: *mut LeanObject,
    mut v___y_7321_: *mut LeanObject,
    mut v___y_7322_: *mut LeanObject,
    mut v___y_7323_: *mut LeanObject,
    mut v___y_7324_: *mut LeanObject,
    mut v___y_7325_: *mut LeanObject,
    mut v___y_7326_: *mut LeanObject,
    mut v___y_7327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7330_: *mut LeanObject = core::ptr::null_mut();
    v___x_7329_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1,
    );
    v___x_7330_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(
        v___x_7329_,
        v___y_7324_,
        v___y_7325_,
        v___y_7326_,
        v___y_7327_,
    );
    return v___x_7330_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed(
    mut v_x_7331_: *mut LeanObject,
    mut v___y_7332_: *mut LeanObject,
    mut v___y_7333_: *mut LeanObject,
    mut v___y_7334_: *mut LeanObject,
    mut v___y_7335_: *mut LeanObject,
    mut v___y_7336_: *mut LeanObject,
    mut v___y_7337_: *mut LeanObject,
    mut v___y_7338_: *mut LeanObject,
    mut v___y_7339_: *mut LeanObject,
    mut v___y_7340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7341_: *mut LeanObject = core::ptr::null_mut();
    v_res_7341_ = l_Lean_Elab_Tactic_evalLiftLets___lam__0(
        v_x_7331_,
        v___y_7332_,
        v___y_7333_,
        v___y_7334_,
        v___y_7335_,
        v___y_7336_,
        v___y_7337_,
        v___y_7338_,
        v___y_7339_,
    );
    lean_dec(v___y_7339_);
    lean_dec_ref(v___y_7338_);
    lean_dec(v___y_7337_);
    lean_dec_ref(v___y_7336_);
    lean_dec(v___y_7335_);
    lean_dec_ref(v___y_7334_);
    lean_dec(v___y_7333_);
    lean_dec_ref(v___y_7332_);
    lean_dec(v_x_7331_);
    return v_res_7341_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLiftLets___lam__1(
    mut v_a_7342_: *mut LeanObject,
    mut v___y_7343_: *mut LeanObject,
    mut v___y_7344_: *mut LeanObject,
    mut v___y_7345_: *mut LeanObject,
    mut v___y_7346_: *mut LeanObject,
    mut v___y_7347_: *mut LeanObject,
    mut v___y_7348_: *mut LeanObject,
    mut v___y_7349_: *mut LeanObject,
    mut v___y_7350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7362_: u8 = 0;
    let mut v___x_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7366_: u8 = 0;
    let mut v_a_7367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7370_: u8 = 0;
    let mut v___x_7372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7352_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_7344_,
                    v___y_7347_,
                    v___y_7348_,
                    v___y_7349_,
                    v___y_7350_,
                );
                if lean_obj_tag(v___x_7352_) == 0 {
                    v_a_7353_ = lean_ctor_get(v___x_7352_, 0);
                    lean_inc(v_a_7353_);
                    lean_dec_ref_known(v___x_7352_, 1);
                    v___x_7354_ = l_Lean_MVarId_liftLets(
                        v_a_7353_,
                        v_a_7342_,
                        v___y_7347_,
                        v___y_7348_,
                        v___y_7349_,
                        v___y_7350_,
                    );
                    if lean_obj_tag(v___x_7354_) == 0 {
                        v_a_7355_ = lean_ctor_get(v___x_7354_, 0);
                        lean_inc(v_a_7355_);
                        lean_dec_ref_known(v___x_7354_, 1);
                        v___x_7356_ = lean_box(0);
                        v___x_7357_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_7357_, 0, v_a_7355_);
                        lean_ctor_set(v___x_7357_, 1, v___x_7356_);
                        v___x_7358_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_7357_,
                            v___y_7344_,
                            v___y_7347_,
                            v___y_7348_,
                            v___y_7349_,
                            v___y_7350_,
                        );
                        return v___x_7358_;
                    } else {
                        v_a_7359_ = lean_ctor_get(v___x_7354_, 0);
                        v_isSharedCheck_7366_ = (!lean_is_exclusive(v___x_7354_)) as u8;
                        if v_isSharedCheck_7366_ == 0 {
                            v___x_7361_ = v___x_7354_;
                            v_isShared_7362_ = v_isSharedCheck_7366_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7359_);
                            lean_dec(v___x_7354_);
                            v___x_7361_ = lean_box(0);
                            v_isShared_7362_ = v_isSharedCheck_7366_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_7342_);
                    v_a_7367_ = lean_ctor_get(v___x_7352_, 0);
                    v_isSharedCheck_7374_ = (!lean_is_exclusive(v___x_7352_)) as u8;
                    if v_isSharedCheck_7374_ == 0 {
                        v___x_7369_ = v___x_7352_;
                        v_isShared_7370_ = v_isSharedCheck_7374_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7367_);
                        lean_dec(v___x_7352_);
                        v___x_7369_ = lean_box(0);
                        v_isShared_7370_ = v_isSharedCheck_7374_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7362_ == 0 {
                    v___x_7364_ = v___x_7361_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7365_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7365_, 0, v_a_7359_);
                    v___x_7364_ = v_reuseFailAlloc_7365_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7364_;
            }
            3 => {
                if v_isShared_7370_ == 0 {
                    v___x_7372_ = v___x_7369_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7373_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7373_, 0, v_a_7367_);
                    v___x_7372_ = v_reuseFailAlloc_7373_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed(
    mut v_a_7375_: *mut LeanObject,
    mut v___y_7376_: *mut LeanObject,
    mut v___y_7377_: *mut LeanObject,
    mut v___y_7378_: *mut LeanObject,
    mut v___y_7379_: *mut LeanObject,
    mut v___y_7380_: *mut LeanObject,
    mut v___y_7381_: *mut LeanObject,
    mut v___y_7382_: *mut LeanObject,
    mut v___y_7383_: *mut LeanObject,
    mut v___y_7384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7385_: *mut LeanObject = core::ptr::null_mut();
    v_res_7385_ = l_Lean_Elab_Tactic_evalLiftLets___lam__1(
        v_a_7375_,
        v___y_7376_,
        v___y_7377_,
        v___y_7378_,
        v___y_7379_,
        v___y_7380_,
        v___y_7381_,
        v___y_7382_,
        v___y_7383_,
    );
    lean_dec(v___y_7383_);
    lean_dec_ref(v___y_7382_);
    lean_dec(v___y_7381_);
    lean_dec_ref(v___y_7380_);
    lean_dec(v___y_7379_);
    lean_dec_ref(v___y_7378_);
    lean_dec(v___y_7377_);
    lean_dec_ref(v___y_7376_);
    return v_res_7385_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLiftLets___lam__2(
    mut v___f_7386_: *mut LeanObject,
    mut v___y_7387_: *mut LeanObject,
    mut v___y_7388_: *mut LeanObject,
    mut v___y_7389_: *mut LeanObject,
    mut v___y_7390_: *mut LeanObject,
    mut v___y_7391_: *mut LeanObject,
    mut v___y_7392_: *mut LeanObject,
    mut v___y_7393_: *mut LeanObject,
    mut v___y_7394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7396_: *mut LeanObject = core::ptr::null_mut();
    v___x_7396_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_7386_,
        v___y_7387_,
        v___y_7388_,
        v___y_7389_,
        v___y_7390_,
        v___y_7391_,
        v___y_7392_,
        v___y_7393_,
        v___y_7394_,
    );
    return v___x_7396_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed(
    mut v___f_7397_: *mut LeanObject,
    mut v___y_7398_: *mut LeanObject,
    mut v___y_7399_: *mut LeanObject,
    mut v___y_7400_: *mut LeanObject,
    mut v___y_7401_: *mut LeanObject,
    mut v___y_7402_: *mut LeanObject,
    mut v___y_7403_: *mut LeanObject,
    mut v___y_7404_: *mut LeanObject,
    mut v___y_7405_: *mut LeanObject,
    mut v___y_7406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7407_: *mut LeanObject = core::ptr::null_mut();
    v_res_7407_ = l_Lean_Elab_Tactic_evalLiftLets___lam__2(
        v___f_7397_,
        v___y_7398_,
        v___y_7399_,
        v___y_7400_,
        v___y_7401_,
        v___y_7402_,
        v___y_7403_,
        v___y_7404_,
        v___y_7405_,
    );
    lean_dec(v___y_7405_);
    lean_dec_ref(v___y_7404_);
    lean_dec(v___y_7403_);
    lean_dec_ref(v___y_7402_);
    lean_dec(v___y_7401_);
    lean_dec_ref(v___y_7400_);
    lean_dec(v___y_7399_);
    lean_dec_ref(v___y_7398_);
    return v_res_7407_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLiftLets___lam__3(
    mut v_h_7408_: *mut LeanObject,
    mut v_a_7409_: *mut LeanObject,
    mut v___y_7410_: *mut LeanObject,
    mut v___y_7411_: *mut LeanObject,
    mut v___y_7412_: *mut LeanObject,
    mut v___y_7413_: *mut LeanObject,
    mut v___y_7414_: *mut LeanObject,
    mut v___y_7415_: *mut LeanObject,
    mut v___y_7416_: *mut LeanObject,
    mut v___y_7417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7429_: u8 = 0;
    let mut v___x_7431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7433_: u8 = 0;
    let mut v_a_7434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7437_: u8 = 0;
    let mut v___x_7439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7419_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_7411_,
                    v___y_7414_,
                    v___y_7415_,
                    v___y_7416_,
                    v___y_7417_,
                );
                if lean_obj_tag(v___x_7419_) == 0 {
                    v_a_7420_ = lean_ctor_get(v___x_7419_, 0);
                    lean_inc(v_a_7420_);
                    lean_dec_ref_known(v___x_7419_, 1);
                    v___x_7421_ = l_Lean_MVarId_liftLetsLocalDecl(
                        v_a_7420_,
                        v_h_7408_,
                        v_a_7409_,
                        v___y_7414_,
                        v___y_7415_,
                        v___y_7416_,
                        v___y_7417_,
                    );
                    if lean_obj_tag(v___x_7421_) == 0 {
                        v_a_7422_ = lean_ctor_get(v___x_7421_, 0);
                        lean_inc(v_a_7422_);
                        lean_dec_ref_known(v___x_7421_, 1);
                        v___x_7423_ = lean_box(0);
                        v___x_7424_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_7424_, 0, v_a_7422_);
                        lean_ctor_set(v___x_7424_, 1, v___x_7423_);
                        v___x_7425_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_7424_,
                            v___y_7411_,
                            v___y_7414_,
                            v___y_7415_,
                            v___y_7416_,
                            v___y_7417_,
                        );
                        return v___x_7425_;
                    } else {
                        v_a_7426_ = lean_ctor_get(v___x_7421_, 0);
                        v_isSharedCheck_7433_ = (!lean_is_exclusive(v___x_7421_)) as u8;
                        if v_isSharedCheck_7433_ == 0 {
                            v___x_7428_ = v___x_7421_;
                            v_isShared_7429_ = v_isSharedCheck_7433_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7426_);
                            lean_dec(v___x_7421_);
                            v___x_7428_ = lean_box(0);
                            v_isShared_7429_ = v_isSharedCheck_7433_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_7409_);
                    lean_dec(v_h_7408_);
                    v_a_7434_ = lean_ctor_get(v___x_7419_, 0);
                    v_isSharedCheck_7441_ = (!lean_is_exclusive(v___x_7419_)) as u8;
                    if v_isSharedCheck_7441_ == 0 {
                        v___x_7436_ = v___x_7419_;
                        v_isShared_7437_ = v_isSharedCheck_7441_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7434_);
                        lean_dec(v___x_7419_);
                        v___x_7436_ = lean_box(0);
                        v_isShared_7437_ = v_isSharedCheck_7441_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7429_ == 0 {
                    v___x_7431_ = v___x_7428_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7432_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7432_, 0, v_a_7426_);
                    v___x_7431_ = v_reuseFailAlloc_7432_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7431_;
            }
            3 => {
                if v_isShared_7437_ == 0 {
                    v___x_7439_ = v___x_7436_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7440_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7440_, 0, v_a_7434_);
                    v___x_7439_ = v_reuseFailAlloc_7440_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7439_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed(
    mut v_h_7442_: *mut LeanObject,
    mut v_a_7443_: *mut LeanObject,
    mut v___y_7444_: *mut LeanObject,
    mut v___y_7445_: *mut LeanObject,
    mut v___y_7446_: *mut LeanObject,
    mut v___y_7447_: *mut LeanObject,
    mut v___y_7448_: *mut LeanObject,
    mut v___y_7449_: *mut LeanObject,
    mut v___y_7450_: *mut LeanObject,
    mut v___y_7451_: *mut LeanObject,
    mut v___y_7452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7453_: *mut LeanObject = core::ptr::null_mut();
    v_res_7453_ = l_Lean_Elab_Tactic_evalLiftLets___lam__3(
        v_h_7442_,
        v_a_7443_,
        v___y_7444_,
        v___y_7445_,
        v___y_7446_,
        v___y_7447_,
        v___y_7448_,
        v___y_7449_,
        v___y_7450_,
        v___y_7451_,
    );
    lean_dec(v___y_7451_);
    lean_dec_ref(v___y_7450_);
    lean_dec(v___y_7449_);
    lean_dec_ref(v___y_7448_);
    lean_dec(v___y_7447_);
    lean_dec_ref(v___y_7446_);
    lean_dec(v___y_7445_);
    lean_dec_ref(v___y_7444_);
    return v_res_7453_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLiftLets___lam__4(
    mut v_a_7454_: *mut LeanObject,
    mut v_h_7455_: *mut LeanObject,
    mut v___y_7456_: *mut LeanObject,
    mut v___y_7457_: *mut LeanObject,
    mut v___y_7458_: *mut LeanObject,
    mut v___y_7459_: *mut LeanObject,
    mut v___y_7460_: *mut LeanObject,
    mut v___y_7461_: *mut LeanObject,
    mut v___y_7462_: *mut LeanObject,
    mut v___y_7463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut LeanObject = core::ptr::null_mut();
    v___f_7465_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed as *mut core::ffi::c_void,
        11,
        2,
    );
    lean_closure_set(v___f_7465_, 0, v_h_7455_);
    lean_closure_set(v___f_7465_, 1, v_a_7454_);
    v___x_7466_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_7465_,
        v___y_7456_,
        v___y_7457_,
        v___y_7458_,
        v___y_7459_,
        v___y_7460_,
        v___y_7461_,
        v___y_7462_,
        v___y_7463_,
    );
    return v___x_7466_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed(
    mut v_a_7467_: *mut LeanObject,
    mut v_h_7468_: *mut LeanObject,
    mut v___y_7469_: *mut LeanObject,
    mut v___y_7470_: *mut LeanObject,
    mut v___y_7471_: *mut LeanObject,
    mut v___y_7472_: *mut LeanObject,
    mut v___y_7473_: *mut LeanObject,
    mut v___y_7474_: *mut LeanObject,
    mut v___y_7475_: *mut LeanObject,
    mut v___y_7476_: *mut LeanObject,
    mut v___y_7477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7478_: *mut LeanObject = core::ptr::null_mut();
    v_res_7478_ = l_Lean_Elab_Tactic_evalLiftLets___lam__4(
        v_a_7467_,
        v_h_7468_,
        v___y_7469_,
        v___y_7470_,
        v___y_7471_,
        v___y_7472_,
        v___y_7473_,
        v___y_7474_,
        v___y_7475_,
        v___y_7476_,
    );
    lean_dec(v___y_7476_);
    lean_dec_ref(v___y_7475_);
    lean_dec(v___y_7474_);
    lean_dec_ref(v___y_7473_);
    lean_dec(v___y_7472_);
    lean_dec_ref(v___y_7471_);
    lean_dec(v___y_7470_);
    lean_dec_ref(v___y_7469_);
    return v_res_7478_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLiftLets(
    mut v_x_7486_: *mut LeanObject,
    mut v_a_7487_: *mut LeanObject,
    mut v_a_7488_: *mut LeanObject,
    mut v_a_7489_: *mut LeanObject,
    mut v_a_7490_: *mut LeanObject,
    mut v_a_7491_: *mut LeanObject,
    mut v_a_7492_: *mut LeanObject,
    mut v_a_7493_: *mut LeanObject,
    mut v_a_7494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7513_: u8 = 0;
    let mut v___x_7514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7518_: u8 = 0;
    let mut v___x_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_loc_x3f_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7531_: u8 = 0;
    let mut v___x_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7542_: u8 = 0;
    let mut v___x_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7546_: u8 = 0;
    let mut v_a_7547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7550_: u8 = 0;
    let mut v___x_7552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7554_: u8 = 0;
    let mut v___x_7555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7557_: u8 = 0;
    let mut v___x_7558_: u8 = 0;
    let mut v___x_7559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_loc_x3f_7561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7563_: u8 = 0;
    let mut v___x_7564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7566_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7512_ = l_Lean_Elab_Tactic_evalLiftLets___closed__1;
                lean_inc(v_x_7486_);
                v___x_7513_ = l_Lean_Syntax_isOfKind(v_x_7486_, v___x_7512_);
                if v___x_7513_ == 0 {
                    lean_dec(v_x_7486_);
                    v___x_7514_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
                    return v___x_7514_;
                } else {
                    v___x_7515_ = lean_unsigned_to_nat(1);
                    v___x_7516_ = l_Lean_Syntax_getArg(v_x_7486_, v___x_7515_);
                    v___x_7517_ = l_Lean_Elab_Tactic_evalExtractLets___closed__4;
                    lean_inc(v___x_7516_);
                    v___x_7518_ = l_Lean_Syntax_isOfKind(v___x_7516_, v___x_7517_);
                    if v___x_7518_ == 0 {
                        lean_dec(v___x_7516_);
                        lean_dec(v_x_7486_);
                        v___x_7519_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
                        return v___x_7519_;
                    } else {
                        v___f_7520_ = l_Lean_Elab_Tactic_evalLiftLets___closed__2;
                        v___x_7555_ = lean_unsigned_to_nat(2);
                        v___x_7556_ = l_Lean_Syntax_getArg(v_x_7486_, v___x_7555_);
                        lean_dec(v_x_7486_);
                        v___x_7557_ = l_Lean_Syntax_isNone(v___x_7556_);
                        if v___x_7557_ == 0 {
                            lean_inc(v___x_7556_);
                            v___x_7558_ = l_Lean_Syntax_matchesNull(v___x_7556_, v___x_7515_);
                            if v___x_7558_ == 0 {
                                lean_dec(v___x_7556_);
                                lean_dec(v___x_7516_);
                                v___x_7559_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
                                return v___x_7559_;
                            } else {
                                v___x_7560_ = lean_unsigned_to_nat(0);
                                v_loc_x3f_7561_ = l_Lean_Syntax_getArg(v___x_7556_, v___x_7560_);
                                lean_dec(v___x_7556_);
                                v___x_7562_ = l_Lean_Elab_Tactic_evalExtractLets___closed__7;
                                lean_inc(v_loc_x3f_7561_);
                                v___x_7563_ = l_Lean_Syntax_isOfKind(v_loc_x3f_7561_, v___x_7562_);
                                if v___x_7563_ == 0 {
                                    lean_dec(v_loc_x3f_7561_);
                                    lean_dec(v___x_7516_);
                                    v___x_7564_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
                                    return v___x_7564_;
                                } else {
                                    v___x_7565_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_7565_, 0, v_loc_x3f_7561_);
                                    v_loc_x3f_7522_ = v___x_7565_;
                                    v___y_7523_ = v_a_7487_;
                                    v___y_7524_ = v_a_7488_;
                                    v___y_7525_ = v_a_7489_;
                                    v___y_7526_ = v_a_7490_;
                                    v___y_7527_ = v_a_7491_;
                                    v___y_7528_ = v_a_7492_;
                                    v___y_7529_ = v_a_7493_;
                                    v___y_7530_ = v_a_7494_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_7556_);
                            v___x_7566_ = lean_box(0);
                            v_loc_x3f_7522_ = v___x_7566_;
                            v___y_7523_ = v_a_7487_;
                            v___y_7524_ = v_a_7488_;
                            v___y_7525_ = v_a_7489_;
                            v___y_7526_ = v_a_7490_;
                            v___y_7527_ = v_a_7491_;
                            v___y_7528_ = v_a_7492_;
                            v___y_7529_ = v_a_7493_;
                            v___y_7530_ = v_a_7494_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7509_ = l_Lean_mkOptionalNode(v___y_7508_);
                v___x_7510_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_7509_);
                lean_dec(v___x_7509_);
                lean_inc_ref(v___y_7503_);
                v___x_7511_ = l_Lean_Elab_Tactic_withLocation(
                    v___x_7510_,
                    v___y_7506_,
                    v___y_7497_,
                    v___y_7503_,
                    v___y_7498_,
                    v___y_7501_,
                    v___y_7507_,
                    v___y_7499_,
                    v___y_7505_,
                    v___y_7500_,
                    v___y_7504_,
                    v___y_7502_,
                );
                lean_dec(v___x_7510_);
                return v___x_7511_;
            }
            2 => {
                v___x_7531_ = 0;
                v___x_7532_ = lean_alloc_ctor(0, 0, (11) as u32);
                lean_ctor_set_uint8(v___x_7532_, 0 as u32, v___x_7531_);
                lean_ctor_set_uint8(v___x_7532_, 1 as u32, v___x_7518_);
                lean_ctor_set_uint8(v___x_7532_, 2 as u32, v___x_7531_);
                lean_ctor_set_uint8(v___x_7532_, 3 as u32, v___x_7518_);
                lean_ctor_set_uint8(v___x_7532_, 4 as u32, v___x_7518_);
                lean_ctor_set_uint8(v___x_7532_, 5 as u32, v___x_7531_);
                lean_ctor_set_uint8(v___x_7532_, 6 as u32, v___x_7518_);
                lean_ctor_set_uint8(v___x_7532_, 7 as u32, v___x_7518_);
                lean_ctor_set_uint8(v___x_7532_, 8 as u32, v___x_7531_);
                lean_ctor_set_uint8(v___x_7532_, 9 as u32, v___x_7518_);
                lean_ctor_set_uint8(v___x_7532_, 10 as u32, v___x_7518_);
                v___x_7533_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(
                    v___x_7516_,
                    v___x_7532_,
                    v___x_7518_,
                    v___y_7523_,
                    v___y_7529_,
                    v___y_7530_,
                );
                if lean_obj_tag(v___x_7533_) == 0 {
                    v_a_7534_ = lean_ctor_get(v___x_7533_, 0);
                    lean_inc_n(v_a_7534_, 2);
                    lean_dec_ref_known(v___x_7533_, 1);
                    v___f_7535_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___f_7535_, 0, v_a_7534_);
                    v___f_7536_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___f_7536_, 0, v___f_7535_);
                    v___f_7537_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    lean_closure_set(v___f_7537_, 0, v_a_7534_);
                    if lean_obj_tag(v_loc_x3f_7522_) == 0 {
                        v___x_7538_ = lean_box(0);
                        v___y_7497_ = v___f_7536_;
                        v___y_7498_ = v___y_7523_;
                        v___y_7499_ = v___y_7526_;
                        v___y_7500_ = v___y_7528_;
                        v___y_7501_ = v___y_7524_;
                        v___y_7502_ = v___y_7530_;
                        v___y_7503_ = v___f_7520_;
                        v___y_7504_ = v___y_7529_;
                        v___y_7505_ = v___y_7527_;
                        v___y_7506_ = v___f_7537_;
                        v___y_7507_ = v___y_7525_;
                        v___y_7508_ = v___x_7538_;
                        state = 1;
                        continue;
                    } else {
                        v_val_7539_ = lean_ctor_get(v_loc_x3f_7522_, 0);
                        v_isSharedCheck_7546_ = (!lean_is_exclusive(v_loc_x3f_7522_)) as u8;
                        if v_isSharedCheck_7546_ == 0 {
                            v___x_7541_ = v_loc_x3f_7522_;
                            v_isShared_7542_ = v_isSharedCheck_7546_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_7539_);
                            lean_dec(v_loc_x3f_7522_);
                            v___x_7541_ = lean_box(0);
                            v_isShared_7542_ = v_isSharedCheck_7546_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_loc_x3f_7522_);
                    v_a_7547_ = lean_ctor_get(v___x_7533_, 0);
                    v_isSharedCheck_7554_ = (!lean_is_exclusive(v___x_7533_)) as u8;
                    if v_isSharedCheck_7554_ == 0 {
                        v___x_7549_ = v___x_7533_;
                        v_isShared_7550_ = v_isSharedCheck_7554_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7547_);
                        lean_dec(v___x_7533_);
                        v___x_7549_ = lean_box(0);
                        v_isShared_7550_ = v_isSharedCheck_7554_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7542_ == 0 {
                    v___x_7544_ = v___x_7541_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7545_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7545_, 0, v_val_7539_);
                    v___x_7544_ = v_reuseFailAlloc_7545_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_7497_ = v___f_7536_;
                v___y_7498_ = v___y_7523_;
                v___y_7499_ = v___y_7526_;
                v___y_7500_ = v___y_7528_;
                v___y_7501_ = v___y_7524_;
                v___y_7502_ = v___y_7530_;
                v___y_7503_ = v___f_7520_;
                v___y_7504_ = v___y_7529_;
                v___y_7505_ = v___y_7527_;
                v___y_7506_ = v___f_7537_;
                v___y_7507_ = v___y_7525_;
                v___y_7508_ = v___x_7544_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_7550_ == 0 {
                    v___x_7552_ = v___x_7549_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7553_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7553_, 0, v_a_7547_);
                    v___x_7552_ = v_reuseFailAlloc_7553_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7552_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalLiftLets___boxed(
    mut v_x_7567_: *mut LeanObject,
    mut v_a_7568_: *mut LeanObject,
    mut v_a_7569_: *mut LeanObject,
    mut v_a_7570_: *mut LeanObject,
    mut v_a_7571_: *mut LeanObject,
    mut v_a_7572_: *mut LeanObject,
    mut v_a_7573_: *mut LeanObject,
    mut v_a_7574_: *mut LeanObject,
    mut v_a_7575_: *mut LeanObject,
    mut v_a_7576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7577_: *mut LeanObject = core::ptr::null_mut();
    v_res_7577_ = l_Lean_Elab_Tactic_evalLiftLets(
        v_x_7567_, v_a_7568_, v_a_7569_, v_a_7570_, v_a_7571_, v_a_7572_, v_a_7573_, v_a_7574_,
        v_a_7575_,
    );
    lean_dec(v_a_7575_);
    lean_dec_ref(v_a_7574_);
    lean_dec(v_a_7573_);
    lean_dec_ref(v_a_7572_);
    lean_dec(v_a_7571_);
    lean_dec_ref(v_a_7570_);
    lean_dec(v_a_7569_);
    lean_dec_ref(v_a_7568_);
    return v_res_7577_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1()
-> *mut LeanObject {
    let mut v___x_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: *mut LeanObject = core::ptr::null_mut();
    v___x_7585_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7586_ = l_Lean_Elab_Tactic_evalLiftLets___closed__1;
    v___x_7587_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1;
    v___x_7588_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalLiftLets___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7589_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7585_,
        v___x_7586_,
        v___x_7587_,
        v___x_7588_,
    );
    return v___x_7589_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___boxed(
    mut v_a_7590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7591_: *mut LeanObject = core::ptr::null_mut();
    v_res_7591_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
    return v_res_7591_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_7593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7594_: *mut LeanObject = core::ptr::null_mut();
    v___x_7593_ = l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0;
    v___x_7594_ = l_Lean_stringToMessageData(v___x_7593_);
    return v___x_7594_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLetToHave___lam__0(
    mut v_x_7595_: *mut LeanObject,
    mut v___y_7596_: *mut LeanObject,
    mut v___y_7597_: *mut LeanObject,
    mut v___y_7598_: *mut LeanObject,
    mut v___y_7599_: *mut LeanObject,
    mut v___y_7600_: *mut LeanObject,
    mut v___y_7601_: *mut LeanObject,
    mut v___y_7602_: *mut LeanObject,
    mut v___y_7603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7606_: *mut LeanObject = core::ptr::null_mut();
    v___x_7605_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1,
    );
    v___x_7606_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(
        v___x_7605_,
        v___y_7600_,
        v___y_7601_,
        v___y_7602_,
        v___y_7603_,
    );
    return v___x_7606_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed(
    mut v_x_7607_: *mut LeanObject,
    mut v___y_7608_: *mut LeanObject,
    mut v___y_7609_: *mut LeanObject,
    mut v___y_7610_: *mut LeanObject,
    mut v___y_7611_: *mut LeanObject,
    mut v___y_7612_: *mut LeanObject,
    mut v___y_7613_: *mut LeanObject,
    mut v___y_7614_: *mut LeanObject,
    mut v___y_7615_: *mut LeanObject,
    mut v___y_7616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7617_: *mut LeanObject = core::ptr::null_mut();
    v_res_7617_ = l_Lean_Elab_Tactic_evalLetToHave___lam__0(
        v_x_7607_,
        v___y_7608_,
        v___y_7609_,
        v___y_7610_,
        v___y_7611_,
        v___y_7612_,
        v___y_7613_,
        v___y_7614_,
        v___y_7615_,
    );
    lean_dec(v___y_7615_);
    lean_dec_ref(v___y_7614_);
    lean_dec(v___y_7613_);
    lean_dec_ref(v___y_7612_);
    lean_dec(v___y_7611_);
    lean_dec_ref(v___y_7610_);
    lean_dec(v___y_7609_);
    lean_dec_ref(v___y_7608_);
    lean_dec(v_x_7607_);
    return v_res_7617_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLetToHave___lam__1(
    mut v___x_7618_: u8,
    mut v___y_7619_: *mut LeanObject,
    mut v___y_7620_: *mut LeanObject,
    mut v___y_7621_: *mut LeanObject,
    mut v___y_7622_: *mut LeanObject,
    mut v___y_7623_: *mut LeanObject,
    mut v___y_7624_: *mut LeanObject,
    mut v___y_7625_: *mut LeanObject,
    mut v___y_7626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7638_: u8 = 0;
    let mut v___x_7640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7642_: u8 = 0;
    let mut v_a_7643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7646_: u8 = 0;
    let mut v___x_7648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7650_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7628_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_7620_,
                    v___y_7623_,
                    v___y_7624_,
                    v___y_7625_,
                    v___y_7626_,
                );
                if lean_obj_tag(v___x_7628_) == 0 {
                    v_a_7629_ = lean_ctor_get(v___x_7628_, 0);
                    lean_inc(v_a_7629_);
                    lean_dec_ref_known(v___x_7628_, 1);
                    v___x_7630_ = l_Lean_MVarId_letToHave(
                        v_a_7629_,
                        v___x_7618_,
                        v___y_7623_,
                        v___y_7624_,
                        v___y_7625_,
                        v___y_7626_,
                    );
                    if lean_obj_tag(v___x_7630_) == 0 {
                        v_a_7631_ = lean_ctor_get(v___x_7630_, 0);
                        lean_inc(v_a_7631_);
                        lean_dec_ref_known(v___x_7630_, 1);
                        v___x_7632_ = lean_box(0);
                        v___x_7633_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_7633_, 0, v_a_7631_);
                        lean_ctor_set(v___x_7633_, 1, v___x_7632_);
                        v___x_7634_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_7633_,
                            v___y_7620_,
                            v___y_7623_,
                            v___y_7624_,
                            v___y_7625_,
                            v___y_7626_,
                        );
                        return v___x_7634_;
                    } else {
                        v_a_7635_ = lean_ctor_get(v___x_7630_, 0);
                        v_isSharedCheck_7642_ = (!lean_is_exclusive(v___x_7630_)) as u8;
                        if v_isSharedCheck_7642_ == 0 {
                            v___x_7637_ = v___x_7630_;
                            v_isShared_7638_ = v_isSharedCheck_7642_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7635_);
                            lean_dec(v___x_7630_);
                            v___x_7637_ = lean_box(0);
                            v_isShared_7638_ = v_isSharedCheck_7642_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_7643_ = lean_ctor_get(v___x_7628_, 0);
                    v_isSharedCheck_7650_ = (!lean_is_exclusive(v___x_7628_)) as u8;
                    if v_isSharedCheck_7650_ == 0 {
                        v___x_7645_ = v___x_7628_;
                        v_isShared_7646_ = v_isSharedCheck_7650_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7643_);
                        lean_dec(v___x_7628_);
                        v___x_7645_ = lean_box(0);
                        v_isShared_7646_ = v_isSharedCheck_7650_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7638_ == 0 {
                    v___x_7640_ = v___x_7637_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7641_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7641_, 0, v_a_7635_);
                    v___x_7640_ = v_reuseFailAlloc_7641_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7640_;
            }
            3 => {
                if v_isShared_7646_ == 0 {
                    v___x_7648_ = v___x_7645_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7649_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7649_, 0, v_a_7643_);
                    v___x_7648_ = v_reuseFailAlloc_7649_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed(
    mut v___x_7651_: *mut LeanObject,
    mut v___y_7652_: *mut LeanObject,
    mut v___y_7653_: *mut LeanObject,
    mut v___y_7654_: *mut LeanObject,
    mut v___y_7655_: *mut LeanObject,
    mut v___y_7656_: *mut LeanObject,
    mut v___y_7657_: *mut LeanObject,
    mut v___y_7658_: *mut LeanObject,
    mut v___y_7659_: *mut LeanObject,
    mut v___y_7660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1775__boxed_7661_: u8 = 0;
    let mut v_res_7662_: *mut LeanObject = core::ptr::null_mut();
    v___x_1775__boxed_7661_ = (lean_unbox(v___x_7651_) as u8);
    v_res_7662_ = l_Lean_Elab_Tactic_evalLetToHave___lam__1(
        v___x_1775__boxed_7661_,
        v___y_7652_,
        v___y_7653_,
        v___y_7654_,
        v___y_7655_,
        v___y_7656_,
        v___y_7657_,
        v___y_7658_,
        v___y_7659_,
    );
    lean_dec(v___y_7659_);
    lean_dec_ref(v___y_7658_);
    lean_dec(v___y_7657_);
    lean_dec_ref(v___y_7656_);
    lean_dec(v___y_7655_);
    lean_dec_ref(v___y_7654_);
    lean_dec(v___y_7653_);
    lean_dec_ref(v___y_7652_);
    return v_res_7662_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLetToHave___lam__3(
    mut v_h_7663_: *mut LeanObject,
    mut v___x_7664_: u8,
    mut v___y_7665_: *mut LeanObject,
    mut v___y_7666_: *mut LeanObject,
    mut v___y_7667_: *mut LeanObject,
    mut v___y_7668_: *mut LeanObject,
    mut v___y_7669_: *mut LeanObject,
    mut v___y_7670_: *mut LeanObject,
    mut v___y_7671_: *mut LeanObject,
    mut v___y_7672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7684_: u8 = 0;
    let mut v___x_7686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7688_: u8 = 0;
    let mut v_a_7689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7692_: u8 = 0;
    let mut v___x_7694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7674_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_7666_,
                    v___y_7669_,
                    v___y_7670_,
                    v___y_7671_,
                    v___y_7672_,
                );
                if lean_obj_tag(v___x_7674_) == 0 {
                    v_a_7675_ = lean_ctor_get(v___x_7674_, 0);
                    lean_inc(v_a_7675_);
                    lean_dec_ref_known(v___x_7674_, 1);
                    v___x_7676_ = l_Lean_MVarId_letToHaveLocalDecl(
                        v_a_7675_,
                        v_h_7663_,
                        v___x_7664_,
                        v___y_7669_,
                        v___y_7670_,
                        v___y_7671_,
                        v___y_7672_,
                    );
                    if lean_obj_tag(v___x_7676_) == 0 {
                        v_a_7677_ = lean_ctor_get(v___x_7676_, 0);
                        lean_inc(v_a_7677_);
                        lean_dec_ref_known(v___x_7676_, 1);
                        v___x_7678_ = lean_box(0);
                        v___x_7679_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_7679_, 0, v_a_7677_);
                        lean_ctor_set(v___x_7679_, 1, v___x_7678_);
                        v___x_7680_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_7679_,
                            v___y_7666_,
                            v___y_7669_,
                            v___y_7670_,
                            v___y_7671_,
                            v___y_7672_,
                        );
                        return v___x_7680_;
                    } else {
                        v_a_7681_ = lean_ctor_get(v___x_7676_, 0);
                        v_isSharedCheck_7688_ = (!lean_is_exclusive(v___x_7676_)) as u8;
                        if v_isSharedCheck_7688_ == 0 {
                            v___x_7683_ = v___x_7676_;
                            v_isShared_7684_ = v_isSharedCheck_7688_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7681_);
                            lean_dec(v___x_7676_);
                            v___x_7683_ = lean_box(0);
                            v_isShared_7684_ = v_isSharedCheck_7688_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_h_7663_);
                    v_a_7689_ = lean_ctor_get(v___x_7674_, 0);
                    v_isSharedCheck_7696_ = (!lean_is_exclusive(v___x_7674_)) as u8;
                    if v_isSharedCheck_7696_ == 0 {
                        v___x_7691_ = v___x_7674_;
                        v_isShared_7692_ = v_isSharedCheck_7696_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7689_);
                        lean_dec(v___x_7674_);
                        v___x_7691_ = lean_box(0);
                        v_isShared_7692_ = v_isSharedCheck_7696_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7684_ == 0 {
                    v___x_7686_ = v___x_7683_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7687_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7687_, 0, v_a_7681_);
                    v___x_7686_ = v_reuseFailAlloc_7687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7686_;
            }
            3 => {
                if v_isShared_7692_ == 0 {
                    v___x_7694_ = v___x_7691_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7695_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7695_, 0, v_a_7689_);
                    v___x_7694_ = v_reuseFailAlloc_7695_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7694_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed(
    mut v_h_7697_: *mut LeanObject,
    mut v___x_7698_: *mut LeanObject,
    mut v___y_7699_: *mut LeanObject,
    mut v___y_7700_: *mut LeanObject,
    mut v___y_7701_: *mut LeanObject,
    mut v___y_7702_: *mut LeanObject,
    mut v___y_7703_: *mut LeanObject,
    mut v___y_7704_: *mut LeanObject,
    mut v___y_7705_: *mut LeanObject,
    mut v___y_7706_: *mut LeanObject,
    mut v___y_7707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1851__boxed_7708_: u8 = 0;
    let mut v_res_7709_: *mut LeanObject = core::ptr::null_mut();
    v___x_1851__boxed_7708_ = (lean_unbox(v___x_7698_) as u8);
    v_res_7709_ = l_Lean_Elab_Tactic_evalLetToHave___lam__3(
        v_h_7697_,
        v___x_1851__boxed_7708_,
        v___y_7699_,
        v___y_7700_,
        v___y_7701_,
        v___y_7702_,
        v___y_7703_,
        v___y_7704_,
        v___y_7705_,
        v___y_7706_,
    );
    lean_dec(v___y_7706_);
    lean_dec_ref(v___y_7705_);
    lean_dec(v___y_7704_);
    lean_dec_ref(v___y_7703_);
    lean_dec(v___y_7702_);
    lean_dec_ref(v___y_7701_);
    lean_dec(v___y_7700_);
    lean_dec_ref(v___y_7699_);
    return v_res_7709_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLetToHave___lam__2(
    mut v___x_7710_: u8,
    mut v_h_7711_: *mut LeanObject,
    mut v___y_7712_: *mut LeanObject,
    mut v___y_7713_: *mut LeanObject,
    mut v___y_7714_: *mut LeanObject,
    mut v___y_7715_: *mut LeanObject,
    mut v___y_7716_: *mut LeanObject,
    mut v___y_7717_: *mut LeanObject,
    mut v___y_7718_: *mut LeanObject,
    mut v___y_7719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7723_: *mut LeanObject = core::ptr::null_mut();
    v___x_7721_ = lean_box((v___x_7710_) as usize);
    v___f_7722_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed as *mut core::ffi::c_void,
        11,
        2,
    );
    lean_closure_set(v___f_7722_, 0, v_h_7711_);
    lean_closure_set(v___f_7722_, 1, v___x_7721_);
    v___x_7723_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_7722_,
        v___y_7712_,
        v___y_7713_,
        v___y_7714_,
        v___y_7715_,
        v___y_7716_,
        v___y_7717_,
        v___y_7718_,
        v___y_7719_,
    );
    return v___x_7723_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed(
    mut v___x_7724_: *mut LeanObject,
    mut v_h_7725_: *mut LeanObject,
    mut v___y_7726_: *mut LeanObject,
    mut v___y_7727_: *mut LeanObject,
    mut v___y_7728_: *mut LeanObject,
    mut v___y_7729_: *mut LeanObject,
    mut v___y_7730_: *mut LeanObject,
    mut v___y_7731_: *mut LeanObject,
    mut v___y_7732_: *mut LeanObject,
    mut v___y_7733_: *mut LeanObject,
    mut v___y_7734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1927__boxed_7735_: u8 = 0;
    let mut v_res_7736_: *mut LeanObject = core::ptr::null_mut();
    v___x_1927__boxed_7735_ = (lean_unbox(v___x_7724_) as u8);
    v_res_7736_ = l_Lean_Elab_Tactic_evalLetToHave___lam__2(
        v___x_1927__boxed_7735_,
        v_h_7725_,
        v___y_7726_,
        v___y_7727_,
        v___y_7728_,
        v___y_7729_,
        v___y_7730_,
        v___y_7731_,
        v___y_7732_,
        v___y_7733_,
    );
    lean_dec(v___y_7733_);
    lean_dec_ref(v___y_7732_);
    lean_dec(v___y_7731_);
    lean_dec_ref(v___y_7730_);
    lean_dec(v___y_7729_);
    lean_dec_ref(v___y_7728_);
    lean_dec(v___y_7727_);
    lean_dec_ref(v___y_7726_);
    return v_res_7736_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalLetToHave(
    mut v_x_7744_: *mut LeanObject,
    mut v_a_7745_: *mut LeanObject,
    mut v_a_7746_: *mut LeanObject,
    mut v_a_7747_: *mut LeanObject,
    mut v_a_7748_: *mut LeanObject,
    mut v_a_7749_: *mut LeanObject,
    mut v_a_7750_: *mut LeanObject,
    mut v_a_7751_: *mut LeanObject,
    mut v_a_7752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7755_: u8 = 0;
    let mut v___x_7756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7778_: u8 = 0;
    let mut v___x_7779_: u8 = 0;
    let mut v___x_7780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_loc_x3f_7782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7784_: u8 = 0;
    let mut v___x_7785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7787_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7754_ = l_Lean_Elab_Tactic_evalLetToHave___closed__1;
                lean_inc(v_x_7744_);
                v___x_7755_ = l_Lean_Syntax_isOfKind(v_x_7744_, v___x_7754_);
                if v___x_7755_ == 0 {
                    lean_dec(v_x_7744_);
                    v___x_7756_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
                    return v___x_7756_;
                } else {
                    v___f_7757_ = l_Lean_Elab_Tactic_evalLetToHave___closed__2;
                    v___x_7758_ = lean_box((v___x_7755_) as usize);
                    v___f_7759_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___f_7759_, 0, v___x_7758_);
                    v___f_7760_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___f_7760_, 0, v___f_7759_);
                    v___x_7761_ = lean_box((v___x_7755_) as usize);
                    v___f_7762_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    lean_closure_set(v___f_7762_, 0, v___x_7761_);
                    v___x_7776_ = lean_unsigned_to_nat(1);
                    v___x_7777_ = l_Lean_Syntax_getArg(v_x_7744_, v___x_7776_);
                    lean_dec(v_x_7744_);
                    v___x_7778_ = l_Lean_Syntax_isNone(v___x_7777_);
                    if v___x_7778_ == 0 {
                        lean_inc(v___x_7777_);
                        v___x_7779_ = l_Lean_Syntax_matchesNull(v___x_7777_, v___x_7776_);
                        if v___x_7779_ == 0 {
                            lean_dec(v___x_7777_);
                            lean_dec_ref(v___f_7762_);
                            lean_dec_ref(v___f_7760_);
                            v___x_7780_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
                            return v___x_7780_;
                        } else {
                            v___x_7781_ = lean_unsigned_to_nat(0);
                            v_loc_x3f_7782_ = l_Lean_Syntax_getArg(v___x_7777_, v___x_7781_);
                            lean_dec(v___x_7777_);
                            v___x_7783_ = l_Lean_Elab_Tactic_evalExtractLets___closed__7;
                            lean_inc(v_loc_x3f_7782_);
                            v___x_7784_ = l_Lean_Syntax_isOfKind(v_loc_x3f_7782_, v___x_7783_);
                            if v___x_7784_ == 0 {
                                lean_dec(v_loc_x3f_7782_);
                                lean_dec_ref(v___f_7762_);
                                lean_dec_ref(v___f_7760_);
                                v___x_7785_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
                                return v___x_7785_;
                            } else {
                                v___x_7786_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_7786_, 0, v_loc_x3f_7782_);
                                v___y_7764_ = v_a_7752_;
                                v___y_7765_ = v_a_7749_;
                                v___y_7766_ = v_a_7751_;
                                v___y_7767_ = v_a_7747_;
                                v___y_7768_ = v_a_7748_;
                                v___y_7769_ = v_a_7746_;
                                v___y_7770_ = v_a_7750_;
                                v___y_7771_ = v_a_7745_;
                                v___y_7772_ = v___x_7786_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_7777_);
                        v___x_7787_ = lean_box(0);
                        v___y_7764_ = v_a_7752_;
                        v___y_7765_ = v_a_7749_;
                        v___y_7766_ = v_a_7751_;
                        v___y_7767_ = v_a_7747_;
                        v___y_7768_ = v_a_7748_;
                        v___y_7769_ = v_a_7746_;
                        v___y_7770_ = v_a_7750_;
                        v___y_7771_ = v_a_7745_;
                        v___y_7772_ = v___x_7787_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7773_ = l_Lean_mkOptionalNode(v___y_7772_);
                v___x_7774_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_7773_);
                lean_dec(v___x_7773_);
                v___x_7775_ = l_Lean_Elab_Tactic_withLocation(
                    v___x_7774_,
                    v___f_7762_,
                    v___f_7760_,
                    v___f_7757_,
                    v___y_7771_,
                    v___y_7769_,
                    v___y_7767_,
                    v___y_7768_,
                    v___y_7765_,
                    v___y_7770_,
                    v___y_7766_,
                    v___y_7764_,
                );
                lean_dec(v___x_7774_);
                return v___x_7775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalLetToHave___boxed(
    mut v_x_7788_: *mut LeanObject,
    mut v_a_7789_: *mut LeanObject,
    mut v_a_7790_: *mut LeanObject,
    mut v_a_7791_: *mut LeanObject,
    mut v_a_7792_: *mut LeanObject,
    mut v_a_7793_: *mut LeanObject,
    mut v_a_7794_: *mut LeanObject,
    mut v_a_7795_: *mut LeanObject,
    mut v_a_7796_: *mut LeanObject,
    mut v_a_7797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7798_: *mut LeanObject = core::ptr::null_mut();
    v_res_7798_ = l_Lean_Elab_Tactic_evalLetToHave(
        v_x_7788_, v_a_7789_, v_a_7790_, v_a_7791_, v_a_7792_, v_a_7793_, v_a_7794_, v_a_7795_,
        v_a_7796_,
    );
    lean_dec(v_a_7796_);
    lean_dec_ref(v_a_7795_);
    lean_dec(v_a_7794_);
    lean_dec_ref(v_a_7793_);
    lean_dec(v_a_7792_);
    lean_dec_ref(v_a_7791_);
    lean_dec(v_a_7790_);
    lean_dec_ref(v_a_7789_);
    return v_res_7798_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1()
-> *mut LeanObject {
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: *mut LeanObject = core::ptr::null_mut();
    v___x_7806_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7807_ = l_Lean_Elab_Tactic_evalLetToHave___closed__1;
    v___x_7808_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1;
    v___x_7809_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalLetToHave___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7810_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7806_,
        v___x_7807_,
        v___x_7808_,
        v___x_7809_,
    );
    return v___x_7810_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___boxed(
    mut v_a_7811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7812_: *mut LeanObject = core::ptr::null_mut();
    v_res_7812_ = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
    return v_res_7812_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Lets(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Lets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Binders(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Tactic_linter_tactic_unusedName = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Elab_Tactic_linter_tactic_unusedName);
    lean_dec_ref(res);
    l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig =
        _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig();
    lean_mark_persistent(
        l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprExtractLetsConfig,
    );
    res = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig =
        _init_l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig();
    lean_mark_persistent(
        l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_instEvalExprLiftLetsConfig,
    );
    res = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Lets_0__Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Lets(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Lets(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Lets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Binders(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Lets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Lets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Lets(builtin);
}
