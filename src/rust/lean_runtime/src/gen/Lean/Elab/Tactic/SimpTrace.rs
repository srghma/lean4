// Lean compiler output
// Module: Lean.Elab.Tactic.SimpTrace
// Imports: Lean.Elab.ElabRules Lean.Elab.Tactic.Simp Lean.Meta.Tactic.TryThis Lean.LibrarySuggestions.Basic
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_SepArray_ofElems, l_Lean_Syntax_TSepArray_getElems___redArg,
    l_Lean_Syntax_isNone, l_Lean_Syntax_unsetTrailing, l_Lean_mkCIdentFrom, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Array_mkArray3___redArg, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getId, l_Lean_Syntax_getKind, l_Lean_Syntax_getOptional_x3f,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node3, l_Lean_Syntax_node5, l_Lean_Syntax_node6,
    l_Lean_replaceRef, lean_erase_macro_scopes,
};
use crate::r#gen::Init::Syntax::{l_Lean_Syntax_setArg, l_Lean_Syntax_setArgs};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::ElabRules::{
    initialize_Lean_Elab_ElabRules, runtime_initialize_Lean_Elab_ElabRules,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::l_Lean_Elab_Tactic_getFVarIds;
use crate::r#gen::Lean::Elab::Tactic::Location::l_Lean_Elab_Tactic_expandLocation;
use crate::r#gen::Lean::Elab::Tactic::Simp::{
    initialize_Lean_Elab_Tactic_Simp, l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg,
    l_Lean_Elab_Tactic_elabSimpConfig___redArg, l_Lean_Elab_Tactic_mkSimpContext,
    l_Lean_Elab_Tactic_mkSimpContext___boxed, l_Lean_Elab_Tactic_mkSimpOnly,
    l_Lean_Elab_Tactic_simpLocation, l_Lean_Elab_Tactic_withSimpDiagnostics___boxed,
    runtime_initialize_Lean_Elab_Tactic_Simp,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::LibrarySuggestions::Basic::{
    initialize_Lean_LibrarySuggestions_Basic, l_Lean_LibrarySuggestions_select,
    runtime_initialize_Lean_LibrarySuggestions_Basic,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_nil,
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::l_Lean_Meta_getSimpTheorems___boxed;
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::l_Lean_Meta_dsimpGoal;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpAll::l_Lean_Meta_simpAll;
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_Context_setAutoUnfold;
use crate::r#gen::Lean::Meta::Tactic::TryThis::{
    initialize_Lean_Meta_Tactic_TryThis, l_Lean_Meta_Tactic_TryThis_addSuggestion,
    runtime_initialize_Lean_Meta_Tactic_TryThis,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getNondepPropHyps;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_backward_privateInPublic_warn, l_Lean_ResolveName_resolveGlobalName,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_10, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 111, 115, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 117, 103, 103, 101, 115, 116, 105, 111, 110, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__5_value) as *mut LeanObject,5678370013779637056 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__7_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 111, 99, 97, 108, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__7_value) as *mut LeanObject,9465394776676179543 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__0_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__0_value) as *mut LeanObject,7383208167966365478 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__2_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__2_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [80, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0_value) as *mut LeanObject;
static mut l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2_value: LeanStringObject<167> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 167, m_capacity: 167, m_length: 166, m_data: [96, 32, 97, 99, 99, 101, 115, 115, 101, 100, 32, 112, 117, 98, 108, 105, 99, 108, 121, 59, 32, 116, 104, 105, 115, 32, 105, 115, 32, 97, 108, 108, 111, 119, 101, 100, 32, 111, 110, 108, 121, 32, 98, 101, 99, 97, 117, 115, 101, 32, 116, 104, 101, 32, 96, 98, 97, 99, 107, 119, 97, 114, 100, 46, 112, 114, 105, 118, 97, 116, 101, 73, 110, 80, 117, 98, 108, 105, 99, 96, 32, 111, 112, 116, 105, 111, 110, 32, 105, 115, 32, 101, 110, 97, 98, 108, 101, 100, 46, 32, 10, 10, 68, 105, 115, 97, 98, 108, 101, 32, 96, 98, 97, 99, 107, 119, 97, 114, 100, 46, 112, 114, 105, 118, 97, 116, 101, 73, 110, 80, 117, 98, 108, 105, 99, 46, 119, 97, 114, 110, 96, 32, 116, 111, 32, 115, 105, 108, 101, 110, 99, 101, 32, 116, 104, 105, 115, 32, 119, 97, 114, 110, 105, 110, 103, 46, 0]};
static mut l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2_value) as *mut LeanObject;
static mut l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__1_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 0]};
static mut l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__1_value) as *mut LeanObject;
pub static l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__1_value) as *mut LeanObject] };
static mut l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2_value) as *mut LeanObject;
static mut l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed as *const core::ffi::c_void, m_arity: 10, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0_value: LeanStringObject<7> =
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
        m_data: [116, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0_value)
                as *mut LeanObject,
            16145843736367156323 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2_value: LeanStringObject<10> =
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
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_getSimpTheorems___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [91, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [44, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [93, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8_value: LeanStringObject<5> =
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
        m_data: [111, 110, 108, 121, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9_value: LeanStringObject<5> =
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
        m_data: [115, 105, 109, 112, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10_value: LeanStringObject<15> =
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
            115, 105, 109, 112, 65, 117, 116, 111, 85, 110, 102, 111, 108, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11_value: LeanStringObject<6> =
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
        m_data: [115, 105, 109, 112, 33, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13_value: LeanStringObject<9> =
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
        m_data: [115, 105, 109, 112, 65, 114, 103, 115, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            115, 105, 109, 112, 84, 114, 97, 99, 101, 65, 114, 103, 115, 82, 101, 115, 116, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15_value: LeanStringObject<10> =
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
static mut l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___closed__0_value: LeanStringObject<10> =
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
        m_data: [115, 105, 109, 112, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___closed__0_value) as *mut LeanObject,
        11133577954908528869 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalSimpTrace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpTrace___closed__2_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_evalSimpTrace___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 1,
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Elab_Tactic_evalSimpTrace___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpTrace___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0_value) as *mut LeanObject,11838348556114416856 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 25 as usize) << 1) | 1) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 40 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0_value) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 25 as usize) << 1) | 1) as *mut LeanObject,((( 32 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 25 as usize) << 1) | 1) as *mut LeanObject,((( 45 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3_value) as *mut LeanObject,((( 32 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4_value) as *mut LeanObject,((( 45 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [115, 105, 109, 112, 65, 108, 108, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value: LeanStringObject<9> =
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
        m_data: [115, 105, 109, 112, 95, 97, 108, 108, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            115, 105, 109, 112, 65, 108, 108, 65, 117, 116, 111, 85, 110, 102, 111, 108, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10_value: LeanStringObject<10> =
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
        m_data: [115, 105, 109, 112, 95, 97, 108, 108, 33, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12_value: LeanStringObject<10> =
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
        m_data: [100, 115, 105, 109, 112, 65, 114, 103, 115, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            115, 105, 109, 112, 65, 108, 108, 84, 114, 97, 99, 101, 65, 114, 103, 115, 82, 101,
            115, 116, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [115, 105, 109, 112, 65, 108, 108, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0_value)
                as *mut LeanObject,
            5617311126917319294 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 65, 108, 108, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0_value) as *mut LeanObject,16202876013099089802 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 42 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 58 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 42 as usize) << 1) | 1) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 42 as usize) << 1) | 1) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3_value) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4_value) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0_value: LeanStringObject<6> =
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
        m_data: [100, 115, 105, 109, 112, 0],
    };
static mut l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            100, 115, 105, 109, 112, 65, 117, 116, 111, 85, 110, 102, 111, 108, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2_value: LeanStringObject<7> =
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
        m_data: [100, 115, 105, 109, 112, 33, 0],
    };
static mut l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3_value: LeanStringObject<19> =
    LeanStringObject {
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
            100, 115, 105, 109, 112, 84, 114, 97, 99, 101, 65, 114, 103, 115, 82, 101, 115, 116, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalDSimpTrace___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [100, 115, 105, 109, 112, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Elab_Tactic_evalDSimpTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDSimpTrace___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDSimpTrace___closed__0_value)
                as *mut LeanObject,
            6718895575348223413 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalDSimpTrace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 68, 83, 105, 109, 112, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0_value) as *mut LeanObject,9851961900287056500 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 82 as usize) << 1) | 1) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 95 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0_value) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 82 as usize) << 1) | 1) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 82 as usize) << 1) | 1) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3_value) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4_value) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(
    mut v_as_4512_: *mut LeanObject,
    mut v_i_4513_: usize,
    mut v_stop_4514_: usize,
    mut v_b_4515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: usize = 0;
    let mut v___x_4519_: usize = 0;
    let mut v___x_4521_: u8 = 0;
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: u8 = 0;
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: u8 = 0;
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: u8 = 0;
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: u8 = 0;
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: u8 = 0;
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: u8 = 0;
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: u8 = 0;
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: u8 = 0;
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: u8 = 0;
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: u8 = 0;
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4521_ = lean_usize_dec_eq(v_i_4513_, v_stop_4514_);
                if v___x_4521_ == 0 {
                    v___x_4522_ = lean_unsigned_to_nat(0);
                    v___x_4523_ = lean_array_uget_borrowed(v_as_4512_, v_i_4513_);
                    v___x_4524_ = l_Lean_Syntax_getArg(v___x_4523_, v___x_4522_);
                    lean_inc(v___x_4523_);
                    v___x_4525_ = l_Lean_Syntax_getKind(v___x_4523_);
                    if lean_obj_tag(v___x_4525_) == 1 {
                        v_pre_4526_ = lean_ctor_get(v___x_4525_, 0);
                        lean_inc(v_pre_4526_);
                        if lean_obj_tag(v_pre_4526_) == 1 {
                            v_pre_4527_ = lean_ctor_get(v_pre_4526_, 0);
                            lean_inc(v_pre_4527_);
                            if lean_obj_tag(v_pre_4527_) == 1 {
                                v_pre_4528_ = lean_ctor_get(v_pre_4527_, 0);
                                lean_inc(v_pre_4528_);
                                if lean_obj_tag(v_pre_4528_) == 1 {
                                    v_pre_4529_ = lean_ctor_get(v_pre_4528_, 0);
                                    if lean_obj_tag(v_pre_4529_) == 0 {
                                        v_str_4530_ = lean_ctor_get(v___x_4525_, 1);
                                        lean_inc_ref(v_str_4530_);
                                        lean_dec_ref_known(v___x_4525_, 2);
                                        v_str_4531_ = lean_ctor_get(v_pre_4526_, 1);
                                        lean_inc_ref(v_str_4531_);
                                        lean_dec_ref_known(v_pre_4526_, 2);
                                        v_str_4532_ = lean_ctor_get(v_pre_4527_, 1);
                                        lean_inc_ref(v_str_4532_);
                                        lean_dec_ref_known(v_pre_4527_, 2);
                                        v_str_4533_ = lean_ctor_get(v_pre_4528_, 1);
                                        lean_inc_ref(v_str_4533_);
                                        lean_dec_ref_known(v_pre_4528_, 2);
                                        v___x_4534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0;
                                        v___x_4535_ = lean_string_dec_eq(v_str_4533_, v___x_4534_);
                                        lean_dec_ref(v_str_4533_);
                                        if v___x_4535_ == 0 {
                                            lean_dec_ref(v_str_4532_);
                                            lean_dec_ref(v_str_4531_);
                                            lean_dec_ref(v_str_4530_);
                                            lean_dec(v___x_4524_);
                                            lean_inc(v___x_4523_);
                                            v___x_4536_ = lean_array_push(v_b_4515_, v___x_4523_);
                                            v___y_4517_ = v___x_4536_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_4537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1;
                                            v___x_4538_ =
                                                lean_string_dec_eq(v_str_4532_, v___x_4537_);
                                            lean_dec_ref(v_str_4532_);
                                            if v___x_4538_ == 0 {
                                                lean_dec_ref(v_str_4531_);
                                                lean_dec_ref(v_str_4530_);
                                                lean_dec(v___x_4524_);
                                                lean_inc(v___x_4523_);
                                                v___x_4539_ =
                                                    lean_array_push(v_b_4515_, v___x_4523_);
                                                v___y_4517_ = v___x_4539_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_4540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2;
                                                v___x_4541_ =
                                                    lean_string_dec_eq(v_str_4531_, v___x_4540_);
                                                lean_dec_ref(v_str_4531_);
                                                if v___x_4541_ == 0 {
                                                    lean_dec_ref(v_str_4530_);
                                                    lean_dec(v___x_4524_);
                                                    lean_inc(v___x_4523_);
                                                    v___x_4542_ =
                                                        lean_array_push(v_b_4515_, v___x_4523_);
                                                    v___y_4517_ = v___x_4542_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_4543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__3;
                                                    v___x_4544_ = lean_string_dec_eq(
                                                        v_str_4530_,
                                                        v___x_4543_,
                                                    );
                                                    lean_dec_ref(v_str_4530_);
                                                    if v___x_4544_ == 0 {
                                                        lean_dec(v___x_4524_);
                                                        lean_inc(v___x_4523_);
                                                        v___x_4545_ =
                                                            lean_array_push(v_b_4515_, v___x_4523_);
                                                        v___y_4517_ = v___x_4545_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_4546_ = lean_unsigned_to_nat(1);
                                                        v___x_4547_ = l_Lean_Syntax_getArg(
                                                            v___x_4524_,
                                                            v___x_4546_,
                                                        );
                                                        v___x_4548_ =
                                                            l_Lean_Syntax_getKind(v___x_4524_);
                                                        if lean_obj_tag(v___x_4548_) == 1 {
                                                            v_pre_4549_ =
                                                                lean_ctor_get(v___x_4548_, 0);
                                                            lean_inc(v_pre_4549_);
                                                            if lean_obj_tag(v_pre_4549_) == 1 {
                                                                v_pre_4550_ =
                                                                    lean_ctor_get(v_pre_4549_, 0);
                                                                lean_inc(v_pre_4550_);
                                                                if lean_obj_tag(v_pre_4550_) == 1 {
                                                                    v_pre_4551_ = lean_ctor_get(
                                                                        v_pre_4550_,
                                                                        0,
                                                                    );
                                                                    lean_inc(v_pre_4551_);
                                                                    if lean_obj_tag(v_pre_4551_)
                                                                        == 1
                                                                    {
                                                                        v_pre_4552_ = lean_ctor_get(
                                                                            v_pre_4551_,
                                                                            0,
                                                                        );
                                                                        if lean_obj_tag(v_pre_4552_)
                                                                            == 0
                                                                        {
                                                                            v_str_4553_ =
                                                                                lean_ctor_get(
                                                                                    v___x_4548_,
                                                                                    1,
                                                                                );
                                                                            lean_inc_ref(
                                                                                v_str_4553_,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v___x_4548_,
                                                                                2,
                                                                            );
                                                                            v_str_4554_ =
                                                                                lean_ctor_get(
                                                                                    v_pre_4549_,
                                                                                    1,
                                                                                );
                                                                            lean_inc_ref(
                                                                                v_str_4554_,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_pre_4549_,
                                                                                2,
                                                                            );
                                                                            v_str_4555_ =
                                                                                lean_ctor_get(
                                                                                    v_pre_4550_,
                                                                                    1,
                                                                                );
                                                                            lean_inc_ref(
                                                                                v_str_4555_,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_pre_4550_,
                                                                                2,
                                                                            );
                                                                            v_str_4556_ =
                                                                                lean_ctor_get(
                                                                                    v_pre_4551_,
                                                                                    1,
                                                                                );
                                                                            lean_inc_ref(
                                                                                v_str_4556_,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_pre_4551_,
                                                                                2,
                                                                            );
                                                                            v___x_4557_ =
                                                                                lean_string_dec_eq(
                                                                                    v_str_4556_,
                                                                                    v___x_4534_,
                                                                                );
                                                                            lean_dec_ref(
                                                                                v_str_4556_,
                                                                            );
                                                                            if v___x_4557_ == 0 {
                                                                                lean_dec_ref(
                                                                                    v_str_4555_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_str_4554_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_str_4553_,
                                                                                );
                                                                                lean_dec(
                                                                                    v___x_4547_,
                                                                                );
                                                                                lean_inc(
                                                                                    v___x_4523_,
                                                                                );
                                                                                v___x_4558_ =
                                                                                    lean_array_push(
                                                                                        v_b_4515_,
                                                                                        v___x_4523_,
                                                                                    );
                                                                                v___y_4517_ =
                                                                                    v___x_4558_;
                                                                                state = 1;
                                                                                continue;
                                                                            } else {
                                                                                v___x_4559_ = lean_string_dec_eq(v_str_4555_, v___x_4537_);
                                                                                lean_dec_ref(
                                                                                    v_str_4555_,
                                                                                );
                                                                                if v___x_4559_ == 0
                                                                                {
                                                                                    lean_dec_ref(
                                                                                        v_str_4554_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_str_4553_,
                                                                                    );
                                                                                    lean_dec(
                                                                                        v___x_4547_,
                                                                                    );
                                                                                    lean_inc(
                                                                                        v___x_4523_,
                                                                                    );
                                                                                    v___x_4560_ = lean_array_push(v_b_4515_, v___x_4523_);
                                                                                    v___y_4517_ =
                                                                                        v___x_4560_;
                                                                                    state = 1;
                                                                                    continue;
                                                                                } else {
                                                                                    v___x_4561_ = lean_string_dec_eq(v_str_4554_, v___x_4540_);
                                                                                    lean_dec_ref(
                                                                                        v_str_4554_,
                                                                                    );
                                                                                    if v___x_4561_
                                                                                        == 0
                                                                                    {
                                                                                        lean_dec_ref(v_str_4553_);
                                                                                        lean_dec(v___x_4547_);
                                                                                        lean_inc(v___x_4523_);
                                                                                        v___x_4562_ = lean_array_push(v_b_4515_, v___x_4523_);
                                                                                        v___y_4517_ = v___x_4562_;
                                                                                        state = 1;
                                                                                        continue;
                                                                                    } else {
                                                                                        v___x_4563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__4;
                                                                                        v___x_4564_ = lean_string_dec_eq(v_str_4553_, v___x_4563_);
                                                                                        lean_dec_ref(v_str_4553_);
                                                                                        if v___x_4564_ == 0 {
lean_dec(v___x_4547_);
lean_inc(v___x_4523_);
v___x_4565_ = lean_array_push(v_b_4515_, v___x_4523_);
v___y_4517_ = v___x_4565_;
state = 1; continue;
} else {
v___x_4566_ = l_Lean_Syntax_getId(v___x_4547_);
lean_dec(v___x_4547_);
v_id_4567_ = lean_erase_macro_scopes(v___x_4566_);
v___x_4568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__6;
v___x_4569_ = lean_name_eq(v_id_4567_, v___x_4568_);
if v___x_4569_ == 0 {
v___x_4570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__8;
v___x_4571_ = lean_name_eq(v_id_4567_, v___x_4570_);
lean_dec(v_id_4567_);
if v___x_4571_ == 0 {
lean_inc(v___x_4523_);
v___x_4572_ = lean_array_push(v_b_4515_, v___x_4523_);
v___y_4517_ = v___x_4572_;
state = 1; continue;
} else {
v___y_4517_ = v_b_4515_;
state = 1; continue;
}
} else {
lean_dec(v_id_4567_);
v___y_4517_ = v_b_4515_;
state = 1; continue;
}
}
                                                                                    }
                                                                                }
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref_known(
                                                                                v_pre_4551_,
                                                                                2,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_pre_4550_,
                                                                                2,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_pre_4549_,
                                                                                2,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v___x_4548_,
                                                                                2,
                                                                            );
                                                                            lean_dec(v___x_4547_);
                                                                            lean_inc(v___x_4523_);
                                                                            v___x_4573_ =
                                                                                lean_array_push(
                                                                                    v_b_4515_,
                                                                                    v___x_4523_,
                                                                                );
                                                                            v___y_4517_ =
                                                                                v___x_4573_;
                                                                            state = 1;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref_known(
                                                                            v_pre_4550_,
                                                                            2,
                                                                        );
                                                                        lean_dec(v_pre_4551_);
                                                                        lean_dec_ref_known(
                                                                            v_pre_4549_,
                                                                            2,
                                                                        );
                                                                        lean_dec_ref_known(
                                                                            v___x_4548_,
                                                                            2,
                                                                        );
                                                                        lean_dec(v___x_4547_);
                                                                        lean_inc(v___x_4523_);
                                                                        v___x_4574_ =
                                                                            lean_array_push(
                                                                                v_b_4515_,
                                                                                v___x_4523_,
                                                                            );
                                                                        v___y_4517_ = v___x_4574_;
                                                                        state = 1;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec_ref_known(
                                                                        v_pre_4549_,
                                                                        2,
                                                                    );
                                                                    lean_dec(v_pre_4550_);
                                                                    lean_dec_ref_known(
                                                                        v___x_4548_,
                                                                        2,
                                                                    );
                                                                    lean_dec(v___x_4547_);
                                                                    lean_inc(v___x_4523_);
                                                                    v___x_4575_ = lean_array_push(
                                                                        v_b_4515_,
                                                                        v___x_4523_,
                                                                    );
                                                                    v___y_4517_ = v___x_4575_;
                                                                    state = 1;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref_known(v___x_4548_, 2);
                                                                lean_dec(v_pre_4549_);
                                                                lean_dec(v___x_4547_);
                                                                lean_inc(v___x_4523_);
                                                                v___x_4576_ = lean_array_push(
                                                                    v_b_4515_,
                                                                    v___x_4523_,
                                                                );
                                                                v___y_4517_ = v___x_4576_;
                                                                state = 1;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec(v___x_4548_);
                                                            lean_dec(v___x_4547_);
                                                            lean_inc(v___x_4523_);
                                                            v___x_4577_ = lean_array_push(
                                                                v_b_4515_,
                                                                v___x_4523_,
                                                            );
                                                            v___y_4517_ = v___x_4577_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref_known(v_pre_4528_, 2);
                                        lean_dec_ref_known(v_pre_4527_, 2);
                                        lean_dec_ref_known(v_pre_4526_, 2);
                                        lean_dec_ref_known(v___x_4525_, 2);
                                        lean_dec(v___x_4524_);
                                        lean_inc(v___x_4523_);
                                        v___x_4578_ = lean_array_push(v_b_4515_, v___x_4523_);
                                        v___y_4517_ = v___x_4578_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v_pre_4527_, 2);
                                    lean_dec(v_pre_4528_);
                                    lean_dec_ref_known(v_pre_4526_, 2);
                                    lean_dec_ref_known(v___x_4525_, 2);
                                    lean_dec(v___x_4524_);
                                    lean_inc(v___x_4523_);
                                    v___x_4579_ = lean_array_push(v_b_4515_, v___x_4523_);
                                    v___y_4517_ = v___x_4579_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_pre_4527_);
                                lean_dec_ref_known(v_pre_4526_, 2);
                                lean_dec_ref_known(v___x_4525_, 2);
                                lean_dec(v___x_4524_);
                                lean_inc(v___x_4523_);
                                v___x_4580_ = lean_array_push(v_b_4515_, v___x_4523_);
                                v___y_4517_ = v___x_4580_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v___x_4525_, 2);
                            lean_dec(v_pre_4526_);
                            lean_dec(v___x_4524_);
                            lean_inc(v___x_4523_);
                            v___x_4581_ = lean_array_push(v_b_4515_, v___x_4523_);
                            v___y_4517_ = v___x_4581_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4525_);
                        lean_dec(v___x_4524_);
                        lean_inc(v___x_4523_);
                        v___x_4582_ = lean_array_push(v_b_4515_, v___x_4523_);
                        v___y_4517_ = v___x_4582_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_4515_;
                }
            }
            1 => {
                v___x_4518_ = 1usize;
                v___x_4519_ = lean_usize_add(v_i_4513_, v___x_4518_);
                v_i_4513_ = v___x_4519_;
                v_b_4515_ = v___y_4517_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___boxed(
    mut v_as_4583_: *mut LeanObject,
    mut v_i_4584_: *mut LeanObject,
    mut v_stop_4585_: *mut LeanObject,
    mut v_b_4586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4587_: usize = 0;
    let mut v_stop_boxed_4588_: usize = 0;
    let mut v_res_4589_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4587_ = lean_unbox_usize(v_i_4584_);
    lean_dec(v_i_4584_);
    v_stop_boxed_4588_ = lean_unbox_usize(v_stop_4585_);
    lean_dec(v_stop_4585_);
    v_res_4589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_as_4583_, v_i_boxed_4587_, v_stop_boxed_4588_, v_b_4586_);
    lean_dec_ref(v_as_4583_);
    return v_res_4589_;
}
pub unsafe fn l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(
    mut v_cfg_4592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nullNode_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNullNode_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_configItems_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: u8 = 0;
    let mut v___x_4605_: u8 = 0;
    let mut v___x_4606_: usize = 0;
    let mut v___x_4607_: usize = 0;
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: usize = 0;
    let mut v___x_4610_: usize = 0;
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4594_ = lean_unsigned_to_nat(0);
                v_nullNode_4595_ = l_Lean_Syntax_getArg(v_cfg_4592_, v___x_4594_);
                v_configItems_4601_ = l_Lean_Syntax_getArgs(v_nullNode_4595_);
                v___x_4602_ = lean_array_get_size(v_configItems_4601_);
                v___x_4603_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0;
                v___x_4604_ = lean_nat_dec_lt(v___x_4594_, v___x_4602_);
                if v___x_4604_ == 0 {
                    lean_dec_ref(v_configItems_4601_);
                    v___y_4597_ = v___x_4603_;
                    state = 1;
                    continue;
                } else {
                    v___x_4605_ = lean_nat_dec_le(v___x_4602_, v___x_4602_);
                    if v___x_4605_ == 0 {
                        if v___x_4604_ == 0 {
                            lean_dec_ref(v_configItems_4601_);
                            v___y_4597_ = v___x_4603_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4606_ = 0usize;
                            v___x_4607_ = lean_usize_of_nat(v___x_4602_);
                            v___x_4608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_configItems_4601_, v___x_4606_, v___x_4607_, v___x_4603_);
                            lean_dec_ref(v_configItems_4601_);
                            v___y_4597_ = v___x_4608_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4609_ = 0usize;
                        v___x_4610_ = lean_usize_of_nat(v___x_4602_);
                        v___x_4611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0(v_configItems_4601_, v___x_4609_, v___x_4610_, v___x_4603_);
                        lean_dec_ref(v_configItems_4601_);
                        v___y_4597_ = v___x_4611_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_newNullNode_4598_ = l_Lean_Syntax_setArgs(v_nullNode_4595_, v___y_4597_);
                v___x_4599_ = l_Lean_Syntax_setArg(v_cfg_4592_, v___x_4594_, v_newNullNode_4598_);
                v___x_4600_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4600_, 0, v___x_4599_);
                return v___x_4600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___boxed(
    mut v_cfg_4612_: *mut LeanObject,
    mut v_a_4613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4614_: *mut LeanObject = core::ptr::null_mut();
    v_res_4614_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_4612_);
    return v_res_4614_;
}
pub unsafe fn l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(
    mut v_cfg_4615_: *mut LeanObject,
    mut v_a_4616_: *mut LeanObject,
    mut v_a_4617_: *mut LeanObject,
    mut v_a_4618_: *mut LeanObject,
    mut v_a_4619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    v___x_4621_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(v_cfg_4615_);
    return v___x_4621_;
}
pub unsafe fn l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___boxed(
    mut v_cfg_4622_: *mut LeanObject,
    mut v_a_4623_: *mut LeanObject,
    mut v_a_4624_: *mut LeanObject,
    mut v_a_4625_: *mut LeanObject,
    mut v_a_4626_: *mut LeanObject,
    mut v_a_4627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4628_: *mut LeanObject = core::ptr::null_mut();
    v_res_4628_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig(
        v_cfg_4622_,
        v_a_4623_,
        v_a_4624_,
        v_a_4625_,
        v_a_4626_,
    );
    lean_dec(v_a_4626_);
    lean_dec_ref(v_a_4625_);
    lean_dec(v_a_4624_);
    lean_dec_ref(v_a_4623_);
    return v_res_4628_;
}
pub unsafe fn l_Lean_Elab_Tactic_mkSimpCallStx(
    mut v_stx_4629_: *mut LeanObject,
    mut v_usedSimps_4630_: *mut LeanObject,
    mut v_a_4631_: *mut LeanObject,
    mut v_a_4632_: *mut LeanObject,
    mut v_a_4633_: *mut LeanObject,
    mut v_a_4634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stx_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4641_: u8 = 0;
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4645_: u8 = 0;
    let mut v_a_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4649_: u8 = 0;
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stx_4636_ = l_Lean_Syntax_unsetTrailing(v_stx_4629_);
                v___x_4637_ = l_Lean_Elab_Tactic_mkSimpOnly(
                    v_stx_4636_,
                    v_usedSimps_4630_,
                    v_a_4631_,
                    v_a_4632_,
                    v_a_4633_,
                    v_a_4634_,
                );
                if lean_obj_tag(v___x_4637_) == 0 {
                    v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
                    v_isSharedCheck_4645_ = (!lean_is_exclusive(v___x_4637_)) as u8;
                    if v_isSharedCheck_4645_ == 0 {
                        v___x_4640_ = v___x_4637_;
                        v_isShared_4641_ = v_isSharedCheck_4645_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4638_);
                        lean_dec(v___x_4637_);
                        v___x_4640_ = lean_box(0);
                        v_isShared_4641_ = v_isSharedCheck_4645_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4646_ = lean_ctor_get(v___x_4637_, 0);
                    v_isSharedCheck_4653_ = (!lean_is_exclusive(v___x_4637_)) as u8;
                    if v_isSharedCheck_4653_ == 0 {
                        v___x_4648_ = v___x_4637_;
                        v_isShared_4649_ = v_isSharedCheck_4653_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4646_);
                        lean_dec(v___x_4637_);
                        v___x_4648_ = lean_box(0);
                        v_isShared_4649_ = v_isSharedCheck_4653_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4641_ == 0 {
                    v___x_4643_ = v___x_4640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4644_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4638_);
                    v___x_4643_ = v_reuseFailAlloc_4644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4643_;
            }
            3 => {
                if v_isShared_4649_ == 0 {
                    v___x_4651_ = v___x_4648_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4652_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4646_);
                    v___x_4651_ = v_reuseFailAlloc_4652_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_mkSimpCallStx___boxed(
    mut v_stx_4654_: *mut LeanObject,
    mut v_usedSimps_4655_: *mut LeanObject,
    mut v_a_4656_: *mut LeanObject,
    mut v_a_4657_: *mut LeanObject,
    mut v_a_4658_: *mut LeanObject,
    mut v_a_4659_: *mut LeanObject,
    mut v_a_4660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4661_: *mut LeanObject = core::ptr::null_mut();
    v_res_4661_ = l_Lean_Elab_Tactic_mkSimpCallStx(
        v_stx_4654_,
        v_usedSimps_4655_,
        v_a_4656_,
        v_a_4657_,
        v_a_4658_,
        v_a_4659_,
    );
    lean_dec(v_a_4659_);
    lean_dec_ref(v_a_4658_);
    lean_dec(v_a_4657_);
    lean_dec_ref(v_a_4656_);
    lean_dec_ref(v_usedSimps_4655_);
    return v_res_4661_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    v___x_4662_ = lean_box(0);
    v___x_4663_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_4664_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4664_, 0, v___x_4663_);
    lean_ctor_set(v___x_4664_, 1, v___x_4662_);
    return v___x_4664_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    v___x_4666_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0);
    v___x_4667_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4667_, 0, v___x_4666_);
    return v___x_4667_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___boxed(
    mut v___y_4668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4669_: *mut LeanObject = core::ptr::null_mut();
    v_res_4669_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(
        );
    return v_res_4669_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(
    mut v_00_u03b1_4670_: *mut LeanObject,
    mut v___y_4671_: *mut LeanObject,
    mut v___y_4672_: *mut LeanObject,
    mut v___y_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
    mut v___y_4676_: *mut LeanObject,
    mut v___y_4677_: *mut LeanObject,
    mut v___y_4678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    v___x_4680_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(
        );
    return v___x_4680_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___boxed(
    mut v_00_u03b1_4681_: *mut LeanObject,
    mut v___y_4682_: *mut LeanObject,
    mut v___y_4683_: *mut LeanObject,
    mut v___y_4684_: *mut LeanObject,
    mut v___y_4685_: *mut LeanObject,
    mut v___y_4686_: *mut LeanObject,
    mut v___y_4687_: *mut LeanObject,
    mut v___y_4688_: *mut LeanObject,
    mut v___y_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4691_: *mut LeanObject = core::ptr::null_mut();
    v_res_4691_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0(
            v_00_u03b1_4681_,
            v___y_4682_,
            v___y_4683_,
            v___y_4684_,
            v___y_4685_,
            v___y_4686_,
            v___y_4687_,
            v___y_4688_,
            v___y_4689_,
        );
    lean_dec(v___y_4689_);
    lean_dec_ref(v___y_4688_);
    lean_dec(v___y_4687_);
    lean_dec_ref(v___y_4686_);
    lean_dec(v___y_4685_);
    lean_dec_ref(v___y_4684_);
    lean_dec(v___y_4683_);
    lean_dec_ref(v___y_4682_);
    return v_res_4691_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpTrace___lam__0(
    mut v___x_4692_: u8,
    mut v_x_4693_: *mut LeanObject,
    mut v___y_4694_: *mut LeanObject,
    mut v___y_4695_: *mut LeanObject,
    mut v___y_4696_: *mut LeanObject,
    mut v___y_4697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    v___x_4699_ = lean_box((v___x_4692_) as usize);
    v___x_4700_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4700_, 0, v___x_4699_);
    return v___x_4700_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpTrace___lam__0___boxed(
    mut v___x_4701_: *mut LeanObject,
    mut v_x_4702_: *mut LeanObject,
    mut v___y_4703_: *mut LeanObject,
    mut v___y_4704_: *mut LeanObject,
    mut v___y_4705_: *mut LeanObject,
    mut v___y_4706_: *mut LeanObject,
    mut v___y_4707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_38778__boxed_4708_: u8 = 0;
    let mut v_res_4709_: *mut LeanObject = core::ptr::null_mut();
    v___x_38778__boxed_4708_ = (lean_unbox(v___x_4701_) as u8);
    v_res_4709_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__0(
        v___x_38778__boxed_4708_,
        v_x_4702_,
        v___y_4703_,
        v___y_4704_,
        v___y_4705_,
        v___y_4706_,
    );
    lean_dec(v___y_4706_);
    lean_dec_ref(v___y_4705_);
    lean_dec(v___y_4704_);
    lean_dec_ref(v___y_4703_);
    lean_dec(v_x_4702_);
    return v_res_4709_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpTrace___lam__1(
    mut v___y_4710_: *mut LeanObject,
    mut v___x_4711_: *mut LeanObject,
    mut v___x_4712_: u8,
    mut v___y_4713_: *mut LeanObject,
    mut v_simprocs_4714_: *mut LeanObject,
    mut v_discharge_x3f_4715_: *mut LeanObject,
    mut v___y_4716_: *mut LeanObject,
    mut v___y_4717_: *mut LeanObject,
    mut v___y_4718_: *mut LeanObject,
    mut v___y_4719_: *mut LeanObject,
    mut v___y_4720_: *mut LeanObject,
    mut v___y_4721_: *mut LeanObject,
    mut v___y_4722_: *mut LeanObject,
    mut v___y_4723_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v___y_4710_) == 0 {
        let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
        v___x_4725_ = lean_mk_empty_array_with_capacity(v___x_4711_);
        v___x_4726_ = lean_alloc_ctor(1, 1, (1) as u32);
        lean_ctor_set(v___x_4726_, 0, v___x_4725_);
        lean_ctor_set_uint8(
            v___x_4726_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_4712_,
        );
        v___x_4727_ = l_Lean_Elab_Tactic_simpLocation(
            v___y_4713_,
            v_simprocs_4714_,
            v_discharge_x3f_4715_,
            v___x_4726_,
            v___y_4716_,
            v___y_4717_,
            v___y_4718_,
            v___y_4719_,
            v___y_4720_,
            v___y_4721_,
            v___y_4722_,
            v___y_4723_,
        );
        return v___x_4727_;
    } else {
        let mut v_val_4728_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
        v_val_4728_ = lean_ctor_get(v___y_4710_, 0);
        v___x_4729_ = l_Lean_Elab_Tactic_expandLocation(v_val_4728_);
        v___x_4730_ = l_Lean_Elab_Tactic_simpLocation(
            v___y_4713_,
            v_simprocs_4714_,
            v_discharge_x3f_4715_,
            v___x_4729_,
            v___y_4716_,
            v___y_4717_,
            v___y_4718_,
            v___y_4719_,
            v___y_4720_,
            v___y_4721_,
            v___y_4722_,
            v___y_4723_,
        );
        return v___x_4730_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(
    mut v___y_4731_: *mut LeanObject,
    mut v___x_4732_: *mut LeanObject,
    mut v___x_4733_: *mut LeanObject,
    mut v___y_4734_: *mut LeanObject,
    mut v_simprocs_4735_: *mut LeanObject,
    mut v_discharge_x3f_4736_: *mut LeanObject,
    mut v___y_4737_: *mut LeanObject,
    mut v___y_4738_: *mut LeanObject,
    mut v___y_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
    mut v___y_4741_: *mut LeanObject,
    mut v___y_4742_: *mut LeanObject,
    mut v___y_4743_: *mut LeanObject,
    mut v___y_4744_: *mut LeanObject,
    mut v___y_4745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_38805__boxed_4746_: u8 = 0;
    let mut v_res_4747_: *mut LeanObject = core::ptr::null_mut();
    v___x_38805__boxed_4746_ = (lean_unbox(v___x_4733_) as u8);
    v_res_4747_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(
        v___y_4731_,
        v___x_4732_,
        v___x_38805__boxed_4746_,
        v___y_4734_,
        v_simprocs_4735_,
        v_discharge_x3f_4736_,
        v___y_4737_,
        v___y_4738_,
        v___y_4739_,
        v___y_4740_,
        v___y_4741_,
        v___y_4742_,
        v___y_4743_,
        v___y_4744_,
    );
    lean_dec(v___y_4744_);
    lean_dec_ref(v___y_4743_);
    lean_dec(v___y_4742_);
    lean_dec_ref(v___y_4741_);
    lean_dec(v___y_4740_);
    lean_dec_ref(v___y_4739_);
    lean_dec(v___y_4738_);
    lean_dec_ref(v___y_4737_);
    lean_dec(v___x_4732_);
    lean_dec(v___y_4731_);
    return v_res_4747_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    v___x_4757_ = l_Array_mkArray0(lean_box(0));
    return v___x_4757_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(
    mut v___x_4758_: *mut LeanObject,
    mut v_as_x27_4759_: *mut LeanObject,
    mut v_b_4760_: *mut LeanObject,
    mut v___y_4761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: u8 = 0;
    let mut v___x_4768_: u8 = 0;
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4759_) == 0 {
                    v___x_4763_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4763_, 0, v_b_4760_);
                    return v___x_4763_;
                } else {
                    v_head_4764_ = lean_ctor_get(v_as_x27_4759_, 0);
                    v_tail_4765_ = lean_ctor_get(v_as_x27_4759_, 1);
                    v_ref_4766_ = lean_ctor_get(v___y_4761_, 5);
                    v___x_4767_ = 1;
                    v___x_4768_ = 0;
                    v___x_4769_ = l_Lean_SourceInfo_fromRef(v_ref_4766_, v___x_4768_);
                    v___x_4770_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1;
                    v___x_4771_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                    v___x_4772_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                    lean_inc(v___x_4769_);
                    v___x_4773_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_4773_, 0, v___x_4769_);
                    lean_ctor_set(v___x_4773_, 1, v___x_4771_);
                    lean_ctor_set(v___x_4773_, 2, v___x_4772_);
                    lean_inc(v_head_4764_);
                    v___x_4774_ = l_Lean_mkCIdentFrom(v___x_4758_, v_head_4764_, v___x_4767_);
                    lean_inc_ref(v___x_4773_);
                    v___x_4775_ = l_Lean_Syntax_node3(
                        v___x_4769_,
                        v___x_4770_,
                        v___x_4773_,
                        v___x_4773_,
                        v___x_4774_,
                    );
                    v___x_4776_ = lean_array_push(v_b_4760_, v___x_4775_);
                    v_as_x27_4759_ = v_tail_4765_;
                    v_b_4760_ = v___x_4776_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___boxed(
    mut v___x_4778_: *mut LeanObject,
    mut v_as_x27_4779_: *mut LeanObject,
    mut v_b_4780_: *mut LeanObject,
    mut v___y_4781_: *mut LeanObject,
    mut v___y_4782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4783_: *mut LeanObject = core::ptr::null_mut();
    v_res_4783_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(
        v___x_4778_,
        v_as_x27_4779_,
        v_b_4780_,
        v___y_4781_,
    );
    lean_dec_ref(v___y_4781_);
    lean_dec(v_as_x27_4779_);
    lean_dec(v___x_4778_);
    return v_res_4783_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(
    mut v_x_4784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: u8 = 0;
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4784_) == 0 {
                    v___x_4785_ = lean_box(0);
                    return v___x_4785_;
                } else {
                    v_head_4786_ = lean_ctor_get(v_x_4784_, 0);
                    v_tail_4787_ = lean_ctor_get(v_x_4784_, 1);
                    v_fst_4788_ = lean_ctor_get(v_head_4786_, 0);
                    v___x_4789_ = l_Lean_isPrivateName(v_fst_4788_);
                    if v___x_4789_ == 0 {
                        v_x_4784_ = v_tail_4787_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_head_4786_);
                        v___x_4791_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4791_, 0, v_head_4786_);
                        return v___x_4791_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5___boxed(
    mut v_x_4792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4793_: *mut LeanObject = core::ptr::null_mut();
    v_res_4793_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_x_4792_);
    lean_dec(v_x_4792_);
    return v_res_4793_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(
    mut v_opts_4794_: *mut LeanObject,
    mut v_opt_4795_: *mut LeanObject,
) -> u8 {
    let mut v_name_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    v_name_4796_ = lean_ctor_get(v_opt_4795_, 0);
    v_defValue_4797_ = lean_ctor_get(v_opt_4795_, 1);
    v_map_4798_ = lean_ctor_get(v_opts_4794_, 0);
    v___x_4799_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4798_,
            v_name_4796_,
        );
    if lean_obj_tag(v___x_4799_) == 0 {
        let mut v___x_4800_: u8 = 0;
        v___x_4800_ = (lean_unbox(v_defValue_4797_) as u8);
        return v___x_4800_;
    } else {
        let mut v_val_4801_: *mut LeanObject = core::ptr::null_mut();
        v_val_4801_ = lean_ctor_get(v___x_4799_, 0);
        lean_inc(v_val_4801_);
        lean_dec_ref_known(v___x_4799_, 1);
        if lean_obj_tag(v_val_4801_) == 1 {
            let mut v_v_4802_: u8 = 0;
            v_v_4802_ = lean_ctor_get_uint8(v_val_4801_, 0 as u32);
            lean_dec_ref_known(v_val_4801_, 0);
            return v_v_4802_;
        } else {
            let mut v___x_4803_: u8 = 0;
            lean_dec(v_val_4801_);
            v___x_4803_ = (lean_unbox(v_defValue_4797_) as u8);
            return v___x_4803_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12___boxed(
    mut v_opts_4804_: *mut LeanObject,
    mut v_opt_4805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4806_: u8 = 0;
    let mut v_r_4807_: *mut LeanObject = core::ptr::null_mut();
    v_res_4806_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_opts_4804_, v_opt_4805_);
    lean_dec_ref(v_opt_4805_);
    lean_dec_ref(v_opts_4804_);
    v_r_4807_ = lean_box((v_res_4806_) as usize);
    return v_r_4807_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(
    mut v_opt_4808_: *mut LeanObject,
    mut v___y_4809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    v_options_4811_ = lean_ctor_get(v___y_4809_, 2);
    v___x_4812_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_4811_, v_opt_4808_);
    v___x_4813_ = lean_box((v___x_4812_) as usize);
    v___x_4814_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4814_, 0, v___x_4813_);
    return v___x_4814_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg___boxed(
    mut v_opt_4815_: *mut LeanObject,
    mut v___y_4816_: *mut LeanObject,
    mut v___y_4817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4818_: *mut LeanObject = core::ptr::null_mut();
    v_res_4818_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_4815_, v___y_4816_);
    lean_dec_ref(v___y_4816_);
    lean_dec_ref(v_opt_4815_);
    return v_res_4818_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(
    mut v_msgData_4819_: *mut LeanObject,
    mut v___y_4820_: *mut LeanObject,
    mut v___y_4821_: *mut LeanObject,
    mut v___y_4822_: *mut LeanObject,
    mut v___y_4823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    v___x_4825_ = lean_st_ref_get(v___y_4823_);
    v_env_4826_ = lean_ctor_get(v___x_4825_, 0);
    lean_inc_ref(v_env_4826_);
    lean_dec(v___x_4825_);
    v___x_4827_ = lean_st_ref_get(v___y_4821_);
    v_mctx_4828_ = lean_ctor_get(v___x_4827_, 0);
    lean_inc_ref(v_mctx_4828_);
    lean_dec(v___x_4827_);
    v_lctx_4829_ = lean_ctor_get(v___y_4820_, 2);
    v_options_4830_ = lean_ctor_get(v___y_4822_, 2);
    lean_inc_ref(v_options_4830_);
    lean_inc_ref(v_lctx_4829_);
    v___x_4831_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4831_, 0, v_env_4826_);
    lean_ctor_set(v___x_4831_, 1, v_mctx_4828_);
    lean_ctor_set(v___x_4831_, 2, v_lctx_4829_);
    lean_ctor_set(v___x_4831_, 3, v_options_4830_);
    v___x_4832_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4832_, 0, v___x_4831_);
    lean_ctor_set(v___x_4832_, 1, v_msgData_4819_);
    v___x_4833_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4833_, 0, v___x_4832_);
    return v___x_4833_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18___boxed(
    mut v_msgData_4834_: *mut LeanObject,
    mut v___y_4835_: *mut LeanObject,
    mut v___y_4836_: *mut LeanObject,
    mut v___y_4837_: *mut LeanObject,
    mut v___y_4838_: *mut LeanObject,
    mut v___y_4839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4840_: *mut LeanObject = core::ptr::null_mut();
    v_res_4840_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msgData_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
    lean_dec(v___y_4838_);
    lean_dec_ref(v___y_4837_);
    lean_dec(v___y_4836_);
    lean_dec_ref(v___y_4835_);
    return v_res_4840_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(
    mut v___y_4848_: u8,
    mut v_suppressElabErrors_4849_: u8,
    mut v_x_4850_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4850_) == 1 {
        let mut v_pre_4851_: *mut LeanObject = core::ptr::null_mut();
        v_pre_4851_ = lean_ctor_get(v_x_4850_, 0);
        match lean_obj_tag(v_pre_4851_) {
            1 => {
                let mut v_pre_4852_: *mut LeanObject = core::ptr::null_mut();
                v_pre_4852_ = lean_ctor_get(v_pre_4851_, 0);
                match lean_obj_tag(v_pre_4852_) {
                    0 => {
                        let mut v_str_4853_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_4854_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4856_: u8 = 0;
                        v_str_4853_ = lean_ctor_get(v_x_4850_, 1);
                        v_str_4854_ = lean_ctor_get(v_pre_4851_, 1);
                        v___x_4855_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__0;
                        v___x_4856_ = lean_string_dec_eq(v_str_4854_, v___x_4855_);
                        if v___x_4856_ == 0 {
                            let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4858_: u8 = 0;
                            v___x_4857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2;
                            v___x_4858_ = lean_string_dec_eq(v_str_4854_, v___x_4857_);
                            if v___x_4858_ == 0 {
                                return v___y_4848_;
                            } else {
                                let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_4860_: u8 = 0;
                                v___x_4859_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__1;
                                v___x_4860_ = lean_string_dec_eq(v_str_4853_, v___x_4859_);
                                if v___x_4860_ == 0 {
                                    return v___y_4848_;
                                } else {
                                    return v_suppressElabErrors_4849_;
                                }
                            }
                        } else {
                            let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4862_: u8 = 0;
                            v___x_4861_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__2;
                            v___x_4862_ = lean_string_dec_eq(v_str_4853_, v___x_4861_);
                            if v___x_4862_ == 0 {
                                return v___y_4848_;
                            } else {
                                return v_suppressElabErrors_4849_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_4863_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_4863_ = lean_ctor_get(v_pre_4852_, 0);
                        if lean_obj_tag(v_pre_4863_) == 0 {
                            let mut v_str_4864_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4865_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4866_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4868_: u8 = 0;
                            v_str_4864_ = lean_ctor_get(v_x_4850_, 1);
                            v_str_4865_ = lean_ctor_get(v_pre_4851_, 1);
                            v_str_4866_ = lean_ctor_get(v_pre_4852_, 1);
                            v___x_4867_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__3;
                            v___x_4868_ = lean_string_dec_eq(v_str_4866_, v___x_4867_);
                            if v___x_4868_ == 0 {
                                return v___y_4848_;
                            } else {
                                let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_4870_: u8 = 0;
                                v___x_4869_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__4;
                                v___x_4870_ = lean_string_dec_eq(v_str_4865_, v___x_4869_);
                                if v___x_4870_ == 0 {
                                    return v___y_4848_;
                                } else {
                                    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_4872_: u8 = 0;
                                    v___x_4871_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__5;
                                    v___x_4872_ = lean_string_dec_eq(v_str_4864_, v___x_4871_);
                                    if v___x_4872_ == 0 {
                                        return v___y_4848_;
                                    } else {
                                        return v_suppressElabErrors_4849_;
                                    }
                                }
                            }
                        } else {
                            return v___y_4848_;
                        }
                    }
                    _ => {
                        return v___y_4848_;
                    }
                }
            }
            0 => {
                let mut v_str_4873_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4875_: u8 = 0;
                v_str_4873_ = lean_ctor_get(v_x_4850_, 1);
                v___x_4874_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___closed__6;
                v___x_4875_ = lean_string_dec_eq(v_str_4873_, v___x_4874_);
                if v___x_4875_ == 0 {
                    return v___y_4848_;
                } else {
                    return v_suppressElabErrors_4849_;
                }
            }
            _ => {
                return v___y_4848_;
            }
        }
    } else {
        return v___y_4848_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed(
    mut v___y_4876_: *mut LeanObject,
    mut v_suppressElabErrors_4877_: *mut LeanObject,
    mut v_x_4878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_39004__boxed_4879_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4880_: u8 = 0;
    let mut v_res_4881_: u8 = 0;
    let mut v_r_4882_: *mut LeanObject = core::ptr::null_mut();
    v___y_39004__boxed_4879_ = (lean_unbox(v___y_4876_) as u8);
    v_suppressElabErrors_boxed_4880_ = (lean_unbox(v_suppressElabErrors_4877_) as u8);
    v_res_4881_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0(v___y_39004__boxed_4879_, v_suppressElabErrors_boxed_4880_, v_x_4878_);
    lean_dec(v_x_4878_);
    v_r_4882_ = lean_box((v_res_4881_) as usize);
    return v_r_4882_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(
    mut v_ref_4884_: *mut LeanObject,
    mut v_msgData_4885_: *mut LeanObject,
    mut v_severity_4886_: u8,
    mut v_isSilent_4887_: u8,
    mut v___y_4888_: *mut LeanObject,
    mut v___y_4889_: *mut LeanObject,
    mut v___y_4890_: *mut LeanObject,
    mut v___y_4891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4897_: u8 = 0;
    let mut v___y_4898_: u8 = 0;
    let mut v___y_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4917_: u8 = 0;
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4928_: u8 = 0;
    let mut v___y_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4931_: u8 = 0;
    let mut v___y_4932_: u8 = 0;
    let mut v___y_4933_: u8 = 0;
    let mut v___y_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4943_: u8 = 0;
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: u8 = 0;
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4953_: u8 = 0;
    let mut v___y_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4957_: u8 = 0;
    let mut v___y_4958_: u8 = 0;
    let mut v___y_4959_: u8 = 0;
    let mut v___y_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4967_: u8 = 0;
    let mut v___y_4968_: u8 = 0;
    let mut v___y_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4972_: u8 = 0;
    let mut v_ref_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: u8 = 0;
    let mut v___y_4979_: u8 = 0;
    let mut v___y_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4984_: u8 = 0;
    let mut v___y_4985_: u8 = 0;
    let mut v___y_4987_: u8 = 0;
    let mut v_fileName_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4992_: u8 = 0;
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: u8 = 0;
    let mut v___x_4997_: u8 = 0;
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: u8 = 0;
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: u8 = 0;
    let mut v___x_5003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4977_ = 2;
                v___x_5002_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4886_, v___x_4977_);
                if v___x_5002_ == 0 {
                    v___y_4987_ = v___x_5002_;
                    state = 10;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_4885_);
                    v___x_5003_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4885_);
                    v___y_4987_ = v___x_5003_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4903_ = lean_st_ref_take(v___y_4902_);
                v_currNamespace_4904_ = lean_ctor_get(v___y_4901_, 6);
                v_openDecls_4905_ = lean_ctor_get(v___y_4901_, 7);
                v_env_4906_ = lean_ctor_get(v___x_4903_, 0);
                v_nextMacroScope_4907_ = lean_ctor_get(v___x_4903_, 1);
                v_ngen_4908_ = lean_ctor_get(v___x_4903_, 2);
                v_auxDeclNGen_4909_ = lean_ctor_get(v___x_4903_, 3);
                v_traceState_4910_ = lean_ctor_get(v___x_4903_, 4);
                v_cache_4911_ = lean_ctor_get(v___x_4903_, 5);
                v_messages_4912_ = lean_ctor_get(v___x_4903_, 6);
                v_infoState_4913_ = lean_ctor_get(v___x_4903_, 7);
                v_snapshotTasks_4914_ = lean_ctor_get(v___x_4903_, 8);
                v_isSharedCheck_4928_ = (!lean_is_exclusive(v___x_4903_)) as u8;
                if v_isSharedCheck_4928_ == 0 {
                    v___x_4916_ = v___x_4903_;
                    v_isShared_4917_ = v_isSharedCheck_4928_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4914_);
                    lean_inc(v_infoState_4913_);
                    lean_inc(v_messages_4912_);
                    lean_inc(v_cache_4911_);
                    lean_inc(v_traceState_4910_);
                    lean_inc(v_auxDeclNGen_4909_);
                    lean_inc(v_ngen_4908_);
                    lean_inc(v_nextMacroScope_4907_);
                    lean_inc(v_env_4906_);
                    lean_dec(v___x_4903_);
                    v___x_4916_ = lean_box(0);
                    v_isShared_4917_ = v_isSharedCheck_4928_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_4905_);
                lean_inc(v_currNamespace_4904_);
                v___x_4918_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4918_, 0, v_currNamespace_4904_);
                lean_ctor_set(v___x_4918_, 1, v_openDecls_4905_);
                v___x_4919_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4919_, 0, v___x_4918_);
                lean_ctor_set(v___x_4919_, 1, v___y_4894_);
                lean_inc_ref(v___y_4895_);
                lean_inc_ref(v___y_4900_);
                v___x_4920_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_4920_, 0, v___y_4900_);
                lean_ctor_set(v___x_4920_, 1, v___y_4899_);
                lean_ctor_set(v___x_4920_, 2, v___y_4896_);
                lean_ctor_set(v___x_4920_, 3, v___y_4895_);
                lean_ctor_set(v___x_4920_, 4, v___x_4919_);
                lean_ctor_set_uint8(
                    v___x_4920_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_4898_,
                );
                lean_ctor_set_uint8(
                    v___x_4920_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_4897_,
                );
                lean_ctor_set_uint8(
                    v___x_4920_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4887_,
                );
                v___x_4921_ = l_Lean_MessageLog_add(v___x_4920_, v_messages_4912_);
                if v_isShared_4917_ == 0 {
                    lean_ctor_set(v___x_4916_, 6, v___x_4921_);
                    v___x_4923_ = v___x_4916_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4927_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_env_4906_);
                    lean_ctor_set(v_reuseFailAlloc_4927_, 1, v_nextMacroScope_4907_);
                    lean_ctor_set(v_reuseFailAlloc_4927_, 2, v_ngen_4908_);
                    lean_ctor_set(v_reuseFailAlloc_4927_, 3, v_auxDeclNGen_4909_);
                    lean_ctor_set(v_reuseFailAlloc_4927_, 4, v_traceState_4910_);
                    lean_ctor_set(v_reuseFailAlloc_4927_, 5, v_cache_4911_);
                    lean_ctor_set(v_reuseFailAlloc_4927_, 6, v___x_4921_);
                    lean_ctor_set(v_reuseFailAlloc_4927_, 7, v_infoState_4913_);
                    lean_ctor_set(v_reuseFailAlloc_4927_, 8, v_snapshotTasks_4914_);
                    v___x_4923_ = v_reuseFailAlloc_4927_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4924_ = lean_st_ref_set(v___y_4902_, v___x_4923_);
                v___x_4925_ = lean_box(0);
                v___x_4926_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4926_, 0, v___x_4925_);
                return v___x_4926_;
            }
            4 => {
                v___x_4938_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4885_,
                    );
                v___x_4939_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v___x_4938_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_);
                v_a_4940_ = lean_ctor_get(v___x_4939_, 0);
                v_isSharedCheck_4953_ = (!lean_is_exclusive(v___x_4939_)) as u8;
                if v_isSharedCheck_4953_ == 0 {
                    v___x_4942_ = v___x_4939_;
                    v_isShared_4943_ = v_isSharedCheck_4953_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_4940_);
                    lean_dec(v___x_4939_);
                    v___x_4942_ = lean_box(0);
                    v_isShared_4943_ = v_isSharedCheck_4953_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_4935_, 2);
                v___x_4944_ = l_Lean_FileMap_toPosition(v___y_4935_, v___y_4936_);
                lean_dec(v___y_4936_);
                v___x_4945_ = l_Lean_FileMap_toPosition(v___y_4935_, v___y_4937_);
                lean_dec(v___y_4937_);
                v___x_4946_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4946_, 0, v___x_4945_);
                v___x_4947_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___closed__0;
                if v___y_4931_ == 0 {
                    lean_del_object(v___x_4942_);
                    lean_dec_ref(v___y_4930_);
                    v___y_4894_ = v_a_4940_;
                    v___y_4895_ = v___x_4947_;
                    v___y_4896_ = v___x_4946_;
                    v___y_4897_ = v___y_4933_;
                    v___y_4898_ = v___y_4932_;
                    v___y_4899_ = v___x_4944_;
                    v___y_4900_ = v___y_4934_;
                    v___y_4901_ = v___y_4890_;
                    v___y_4902_ = v___y_4891_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4940_);
                    v___x_4948_ = l_Lean_MessageData_hasTag(v___y_4930_, v_a_4940_);
                    if v___x_4948_ == 0 {
                        lean_dec_ref_known(v___x_4946_, 1);
                        lean_dec_ref(v___x_4944_);
                        lean_dec(v_a_4940_);
                        v___x_4949_ = lean_box(0);
                        if v_isShared_4943_ == 0 {
                            lean_ctor_set(v___x_4942_, 0, v___x_4949_);
                            v___x_4951_ = v___x_4942_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4949_);
                            v___x_4951_ = v_reuseFailAlloc_4952_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4942_);
                        v___y_4894_ = v_a_4940_;
                        v___y_4895_ = v___x_4947_;
                        v___y_4896_ = v___x_4946_;
                        v___y_4897_ = v___y_4933_;
                        v___y_4898_ = v___y_4932_;
                        v___y_4899_ = v___x_4944_;
                        v___y_4900_ = v___y_4934_;
                        v___y_4901_ = v___y_4890_;
                        v___y_4902_ = v___y_4891_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4951_;
            }
            7 => {
                v___x_4963_ = l_Lean_Syntax_getTailPos_x3f(v___y_4956_, v___y_4959_);
                lean_dec(v___y_4956_);
                if lean_obj_tag(v___x_4963_) == 0 {
                    lean_inc(v___y_4962_);
                    v___y_4930_ = v___y_4955_;
                    v___y_4931_ = v___y_4957_;
                    v___y_4932_ = v___y_4959_;
                    v___y_4933_ = v___y_4958_;
                    v___y_4934_ = v___y_4960_;
                    v___y_4935_ = v___y_4961_;
                    v___y_4936_ = v___y_4962_;
                    v___y_4937_ = v___y_4962_;
                    state = 4;
                    continue;
                } else {
                    v_val_4964_ = lean_ctor_get(v___x_4963_, 0);
                    lean_inc(v_val_4964_);
                    lean_dec_ref_known(v___x_4963_, 1);
                    v___y_4930_ = v___y_4955_;
                    v___y_4931_ = v___y_4957_;
                    v___y_4932_ = v___y_4959_;
                    v___y_4933_ = v___y_4958_;
                    v___y_4934_ = v___y_4960_;
                    v___y_4935_ = v___y_4961_;
                    v___y_4936_ = v___y_4962_;
                    v___y_4937_ = v_val_4964_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_4973_ = l_Lean_replaceRef(v_ref_4884_, v___y_4971_);
                v___x_4974_ = l_Lean_Syntax_getPos_x3f(v_ref_4973_, v___y_4968_);
                if lean_obj_tag(v___x_4974_) == 0 {
                    v___x_4975_ = lean_unsigned_to_nat(0);
                    v___y_4955_ = v___y_4966_;
                    v___y_4956_ = v_ref_4973_;
                    v___y_4957_ = v___y_4967_;
                    v___y_4958_ = v___y_4972_;
                    v___y_4959_ = v___y_4968_;
                    v___y_4960_ = v___y_4969_;
                    v___y_4961_ = v___y_4970_;
                    v___y_4962_ = v___x_4975_;
                    state = 7;
                    continue;
                } else {
                    v_val_4976_ = lean_ctor_get(v___x_4974_, 0);
                    lean_inc(v_val_4976_);
                    lean_dec_ref_known(v___x_4974_, 1);
                    v___y_4955_ = v___y_4966_;
                    v___y_4956_ = v_ref_4973_;
                    v___y_4957_ = v___y_4967_;
                    v___y_4958_ = v___y_4972_;
                    v___y_4959_ = v___y_4968_;
                    v___y_4960_ = v___y_4969_;
                    v___y_4961_ = v___y_4970_;
                    v___y_4962_ = v_val_4976_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_4985_ == 0 {
                    v___y_4966_ = v___y_4981_;
                    v___y_4967_ = v___y_4979_;
                    v___y_4968_ = v___y_4984_;
                    v___y_4969_ = v___y_4980_;
                    v___y_4970_ = v___y_4982_;
                    v___y_4971_ = v___y_4983_;
                    v___y_4972_ = v_severity_4886_;
                    state = 8;
                    continue;
                } else {
                    v___y_4966_ = v___y_4981_;
                    v___y_4967_ = v___y_4979_;
                    v___y_4968_ = v___y_4984_;
                    v___y_4969_ = v___y_4980_;
                    v___y_4970_ = v___y_4982_;
                    v___y_4971_ = v___y_4983_;
                    v___y_4972_ = v___x_4977_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_4987_ == 0 {
                    v_fileName_4988_ = lean_ctor_get(v___y_4890_, 0);
                    v_fileMap_4989_ = lean_ctor_get(v___y_4890_, 1);
                    v_options_4990_ = lean_ctor_get(v___y_4890_, 2);
                    v_ref_4991_ = lean_ctor_get(v___y_4890_, 5);
                    v_suppressElabErrors_4992_ = lean_ctor_get_uint8(
                        v___y_4890_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4993_ = lean_box((v___y_4987_) as usize);
                    v___x_4994_ = lean_box((v_suppressElabErrors_4992_) as usize);
                    v___f_4995_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_4995_, 0, v___x_4993_);
                    lean_closure_set(v___f_4995_, 1, v___x_4994_);
                    v___x_4996_ = 1;
                    v___x_4997_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4886_, v___x_4996_);
                    if v___x_4997_ == 0 {
                        v___y_4979_ = v_suppressElabErrors_4992_;
                        v___y_4980_ = v_fileName_4988_;
                        v___y_4981_ = v___f_4995_;
                        v___y_4982_ = v_fileMap_4989_;
                        v___y_4983_ = v_ref_4991_;
                        v___y_4984_ = v___y_4987_;
                        v___y_4985_ = v___x_4997_;
                        state = 9;
                        continue;
                    } else {
                        v___x_4998_ = l_Lean_warningAsError;
                        v___x_4999_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8_spec__12(v_options_4990_, v___x_4998_);
                        v___y_4979_ = v_suppressElabErrors_4992_;
                        v___y_4980_ = v_fileName_4988_;
                        v___y_4981_ = v___f_4995_;
                        v___y_4982_ = v_fileMap_4989_;
                        v___y_4983_ = v_ref_4991_;
                        v___y_4984_ = v___y_4987_;
                        v___y_4985_ = v___x_4999_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_4885_);
                    v___x_5000_ = lean_box(0);
                    v___x_5001_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5001_, 0, v___x_5000_);
                    return v___x_5001_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg___boxed(
    mut v_ref_5004_: *mut LeanObject,
    mut v_msgData_5005_: *mut LeanObject,
    mut v_severity_5006_: *mut LeanObject,
    mut v_isSilent_5007_: *mut LeanObject,
    mut v___y_5008_: *mut LeanObject,
    mut v___y_5009_: *mut LeanObject,
    mut v___y_5010_: *mut LeanObject,
    mut v___y_5011_: *mut LeanObject,
    mut v___y_5012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5013_: u8 = 0;
    let mut v_isSilent_boxed_5014_: u8 = 0;
    let mut v_res_5015_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5013_ = (lean_unbox(v_severity_5006_) as u8);
    v_isSilent_boxed_5014_ = (lean_unbox(v_isSilent_5007_) as u8);
    v_res_5015_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_5004_, v_msgData_5005_, v_severity_boxed_5013_, v_isSilent_boxed_5014_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
    lean_dec(v___y_5011_);
    lean_dec_ref(v___y_5010_);
    lean_dec(v___y_5009_);
    lean_dec_ref(v___y_5008_);
    lean_dec(v_ref_5004_);
    return v_res_5015_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(
    mut v_msgData_5016_: *mut LeanObject,
    mut v_severity_5017_: u8,
    mut v_isSilent_5018_: u8,
    mut v___y_5019_: *mut LeanObject,
    mut v___y_5020_: *mut LeanObject,
    mut v___y_5021_: *mut LeanObject,
    mut v___y_5022_: *mut LeanObject,
    mut v___y_5023_: *mut LeanObject,
    mut v___y_5024_: *mut LeanObject,
    mut v___y_5025_: *mut LeanObject,
    mut v___y_5026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5028_ = lean_ctor_get(v___y_5025_, 5);
    v___x_5029_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_5028_, v_msgData_5016_, v_severity_5017_, v_isSilent_5018_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
    return v___x_5029_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14___boxed(
    mut v_msgData_5030_: *mut LeanObject,
    mut v_severity_5031_: *mut LeanObject,
    mut v_isSilent_5032_: *mut LeanObject,
    mut v___y_5033_: *mut LeanObject,
    mut v___y_5034_: *mut LeanObject,
    mut v___y_5035_: *mut LeanObject,
    mut v___y_5036_: *mut LeanObject,
    mut v___y_5037_: *mut LeanObject,
    mut v___y_5038_: *mut LeanObject,
    mut v___y_5039_: *mut LeanObject,
    mut v___y_5040_: *mut LeanObject,
    mut v___y_5041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5042_: u8 = 0;
    let mut v_isSilent_boxed_5043_: u8 = 0;
    let mut v_res_5044_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5042_ = (lean_unbox(v_severity_5031_) as u8);
    v_isSilent_boxed_5043_ = (lean_unbox(v_isSilent_5032_) as u8);
    v_res_5044_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_5030_, v_severity_boxed_5042_, v_isSilent_boxed_5043_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
    lean_dec(v___y_5040_);
    lean_dec_ref(v___y_5039_);
    lean_dec(v___y_5038_);
    lean_dec_ref(v___y_5037_);
    lean_dec(v___y_5036_);
    lean_dec_ref(v___y_5035_);
    lean_dec(v___y_5034_);
    lean_dec_ref(v___y_5033_);
    return v_res_5044_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(
    mut v_msgData_5045_: *mut LeanObject,
    mut v___y_5046_: *mut LeanObject,
    mut v___y_5047_: *mut LeanObject,
    mut v___y_5048_: *mut LeanObject,
    mut v___y_5049_: *mut LeanObject,
    mut v___y_5050_: *mut LeanObject,
    mut v___y_5051_: *mut LeanObject,
    mut v___y_5052_: *mut LeanObject,
    mut v___y_5053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5055_: u8 = 0;
    let mut v___x_5056_: u8 = 0;
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    v___x_5055_ = 1;
    v___x_5056_ = 0;
    v___x_5057_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14(v_msgData_5045_, v___x_5055_, v___x_5056_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_);
    return v___x_5057_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9___boxed(
    mut v_msgData_5058_: *mut LeanObject,
    mut v___y_5059_: *mut LeanObject,
    mut v___y_5060_: *mut LeanObject,
    mut v___y_5061_: *mut LeanObject,
    mut v___y_5062_: *mut LeanObject,
    mut v___y_5063_: *mut LeanObject,
    mut v___y_5064_: *mut LeanObject,
    mut v___y_5065_: *mut LeanObject,
    mut v___y_5066_: *mut LeanObject,
    mut v___y_5067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5068_: *mut LeanObject = core::ptr::null_mut();
    v_res_5068_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v_msgData_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_);
    lean_dec(v___y_5066_);
    lean_dec_ref(v___y_5065_);
    lean_dec(v___y_5064_);
    lean_dec_ref(v___y_5063_);
    lean_dec(v___y_5062_);
    lean_dec_ref(v___y_5061_);
    lean_dec(v___y_5060_);
    lean_dec_ref(v___y_5059_);
    return v_res_5068_;
}
pub unsafe fn _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1()
-> *mut LeanObject {
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    v___x_5070_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__0;
    v___x_5071_ = l_Lean_stringToMessageData(v___x_5070_);
    return v___x_5071_;
}
pub unsafe fn _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3()
-> *mut LeanObject {
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    v___x_5073_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__2;
    v___x_5074_ = l_Lean_stringToMessageData(v___x_5073_);
    return v___x_5074_;
}
pub unsafe fn l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(
    mut v_id_5075_: *mut LeanObject,
    mut v___y_5076_: *mut LeanObject,
    mut v___y_5077_: *mut LeanObject,
    mut v___y_5078_: *mut LeanObject,
    mut v___y_5079_: *mut LeanObject,
    mut v___y_5080_: *mut LeanObject,
    mut v___y_5081_: *mut LeanObject,
    mut v___y_5082_: *mut LeanObject,
    mut v___y_5083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5092_: u8 = 0;
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_5098_: u8 = 0;
    let mut v___x_5099_: u8 = 0;
    let mut v___x_5100_: u8 = 0;
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: u8 = 0;
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5108_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5085_ = lean_st_ref_get(v___y_5083_);
                v_env_5086_ = lean_ctor_get(v___x_5085_, 0);
                lean_inc_ref(v_env_5086_);
                lean_dec(v___x_5085_);
                v___x_5087_ = l_Lean_ResolveName_backward_privateInPublic_warn;
                v___x_5088_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v___x_5087_, v___y_5082_);
                v_a_5089_ = lean_ctor_get(v___x_5088_, 0);
                v_isSharedCheck_5108_ = (!lean_is_exclusive(v___x_5088_)) as u8;
                if v_isSharedCheck_5108_ == 0 {
                    v___x_5091_ = v___x_5088_;
                    v_isShared_5092_ = v_isSharedCheck_5108_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5089_);
                    lean_dec(v___x_5088_);
                    v___x_5091_ = lean_box(0);
                    v_isShared_5092_ = v_isSharedCheck_5108_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_isExporting_5098_ = lean_ctor_get_uint8(
                    v_env_5086_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_5086_);
                if v_isExporting_5098_ == 0 {
                    lean_dec(v_a_5089_);
                    lean_dec(v_id_5075_);
                    state = 2;
                    continue;
                } else {
                    v___x_5099_ = l_Lean_isPrivateName(v_id_5075_);
                    if v___x_5099_ == 0 {
                        lean_dec(v_a_5089_);
                        lean_dec(v_id_5075_);
                        state = 2;
                        continue;
                    } else {
                        v___x_5100_ = (lean_unbox(v_a_5089_) as u8);
                        lean_dec(v_a_5089_);
                        if v___x_5100_ == 0 {
                            lean_dec(v_id_5075_);
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_5091_);
                            v___x_5101_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1), core::ptr::addr_of_mut!(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1_once), _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__1);
                            v___x_5102_ = 0;
                            v___x_5103_ = l_Lean_MessageData_ofConstName(v_id_5075_, v___x_5102_);
                            v___x_5104_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5104_, 0, v___x_5101_);
                            lean_ctor_set(v___x_5104_, 1, v___x_5103_);
                            v___x_5105_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3), core::ptr::addr_of_mut!(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3_once), _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___closed__3);
                            v___x_5106_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5106_, 0, v___x_5104_);
                            lean_ctor_set(v___x_5106_, 1, v___x_5105_);
                            v___x_5107_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9(v___x_5106_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_);
                            return v___x_5107_;
                        }
                    }
                }
            }
            2 => {
                v___x_5094_ = lean_box(0);
                if v_isShared_5092_ == 0 {
                    lean_ctor_set(v___x_5091_, 0, v___x_5094_);
                    v___x_5096_ = v___x_5091_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5097_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5097_, 0, v___x_5094_);
                    v___x_5096_ = v_reuseFailAlloc_5097_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6___boxed(
    mut v_id_5109_: *mut LeanObject,
    mut v___y_5110_: *mut LeanObject,
    mut v___y_5111_: *mut LeanObject,
    mut v___y_5112_: *mut LeanObject,
    mut v___y_5113_: *mut LeanObject,
    mut v___y_5114_: *mut LeanObject,
    mut v___y_5115_: *mut LeanObject,
    mut v___y_5116_: *mut LeanObject,
    mut v___y_5117_: *mut LeanObject,
    mut v___y_5118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5119_: *mut LeanObject = core::ptr::null_mut();
    v_res_5119_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_id_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
    lean_dec(v___y_5117_);
    lean_dec_ref(v___y_5116_);
    lean_dec(v___y_5115_);
    lean_dec_ref(v___y_5114_);
    lean_dec(v___y_5113_);
    lean_dec_ref(v___y_5112_);
    lean_dec(v___y_5111_);
    lean_dec_ref(v___y_5110_);
    return v_res_5119_;
}
pub unsafe fn l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(
    mut v_id_5120_: *mut LeanObject,
    mut v_enableLog_5121_: u8,
    mut v___y_5122_: *mut LeanObject,
    mut v___y_5123_: *mut LeanObject,
    mut v___y_5124_: *mut LeanObject,
    mut v___y_5125_: *mut LeanObject,
    mut v___y_5126_: *mut LeanObject,
    mut v___y_5127_: *mut LeanObject,
    mut v___y_5128_: *mut LeanObject,
    mut v___y_5129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_5140_: u8 = 0;
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5148_: u8 = 0;
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5152_: u8 = 0;
    let mut v_unused_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5157_: u8 = 0;
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5161_: u8 = 0;
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5131_ = lean_st_ref_get(v___y_5129_);
                v_env_5132_ = lean_ctor_get(v___x_5131_, 0);
                lean_inc_ref(v_env_5132_);
                lean_dec(v___x_5131_);
                v_options_5133_ = lean_ctor_get(v___y_5128_, 2);
                v_currNamespace_5134_ = lean_ctor_get(v___y_5128_, 6);
                v_openDecls_5135_ = lean_ctor_get(v___y_5128_, 7);
                v___x_5136_ = lean_st_ref_get(v___y_5129_);
                v_env_5137_ = lean_ctor_get(v___x_5136_, 0);
                lean_inc_ref(v_env_5137_);
                lean_dec(v___x_5136_);
                lean_inc(v_openDecls_5135_);
                lean_inc(v_currNamespace_5134_);
                v_res_5138_ = l_Lean_ResolveName_resolveGlobalName(
                    v_env_5132_,
                    v_options_5133_,
                    v_currNamespace_5134_,
                    v_openDecls_5135_,
                    v_id_5120_,
                );
                if v_enableLog_5121_ == 0 {
                    lean_dec_ref(v_env_5137_);
                    v___x_5139_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5139_, 0, v_res_5138_);
                    return v___x_5139_;
                } else {
                    v_isExporting_5140_ = lean_ctor_get_uint8(
                        v_env_5137_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    lean_dec_ref(v_env_5137_);
                    if v_isExporting_5140_ == 0 {
                        v___x_5141_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5141_, 0, v_res_5138_);
                        return v___x_5141_;
                    } else {
                        v___x_5142_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__5(v_res_5138_);
                        if lean_obj_tag(v___x_5142_) == 1 {
                            v_val_5143_ = lean_ctor_get(v___x_5142_, 0);
                            lean_inc(v_val_5143_);
                            lean_dec_ref_known(v___x_5142_, 1);
                            v_fst_5144_ = lean_ctor_get(v_val_5143_, 0);
                            lean_inc(v_fst_5144_);
                            lean_dec(v_val_5143_);
                            v___x_5145_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6(v_fst_5144_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_);
                            if lean_obj_tag(v___x_5145_) == 0 {
                                v_isSharedCheck_5152_ = (!lean_is_exclusive(v___x_5145_)) as u8;
                                if v_isSharedCheck_5152_ == 0 {
                                    v_unused_5153_ = lean_ctor_get(v___x_5145_, 0);
                                    lean_dec(v_unused_5153_);
                                    v___x_5147_ = v___x_5145_;
                                    v_isShared_5148_ = v_isSharedCheck_5152_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___x_5145_);
                                    v___x_5147_ = lean_box(0);
                                    v_isShared_5148_ = v_isSharedCheck_5152_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_res_5138_);
                                v_a_5154_ = lean_ctor_get(v___x_5145_, 0);
                                v_isSharedCheck_5161_ = (!lean_is_exclusive(v___x_5145_)) as u8;
                                if v_isSharedCheck_5161_ == 0 {
                                    v___x_5156_ = v___x_5145_;
                                    v_isShared_5157_ = v_isSharedCheck_5161_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_5154_);
                                    lean_dec(v___x_5145_);
                                    v___x_5156_ = lean_box(0);
                                    v_isShared_5157_ = v_isSharedCheck_5161_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_5142_);
                            v___x_5162_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5162_, 0, v_res_5138_);
                            return v___x_5162_;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5148_ == 0 {
                    lean_ctor_set(v___x_5147_, 0, v_res_5138_);
                    v___x_5150_ = v___x_5147_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5151_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_res_5138_);
                    v___x_5150_ = v_reuseFailAlloc_5151_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5150_;
            }
            3 => {
                if v_isShared_5157_ == 0 {
                    v___x_5159_ = v___x_5156_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5160_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5160_, 0, v_a_5154_);
                    v___x_5159_ = v_reuseFailAlloc_5160_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2___boxed(
    mut v_id_5163_: *mut LeanObject,
    mut v_enableLog_5164_: *mut LeanObject,
    mut v___y_5165_: *mut LeanObject,
    mut v___y_5166_: *mut LeanObject,
    mut v___y_5167_: *mut LeanObject,
    mut v___y_5168_: *mut LeanObject,
    mut v___y_5169_: *mut LeanObject,
    mut v___y_5170_: *mut LeanObject,
    mut v___y_5171_: *mut LeanObject,
    mut v___y_5172_: *mut LeanObject,
    mut v___y_5173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enableLog_boxed_5174_: u8 = 0;
    let mut v_res_5175_: *mut LeanObject = core::ptr::null_mut();
    v_enableLog_boxed_5174_ = (lean_unbox(v_enableLog_5164_) as u8);
    v_res_5175_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_id_5163_, v_enableLog_boxed_5174_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_);
    lean_dec(v___y_5172_);
    lean_dec_ref(v___y_5171_);
    lean_dec(v___y_5170_);
    lean_dec_ref(v___y_5169_);
    lean_dec(v___y_5168_);
    lean_dec_ref(v___y_5167_);
    lean_dec(v___y_5166_);
    lean_dec_ref(v___y_5165_);
    return v_res_5175_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(
    mut v_a_5176_: *mut LeanObject,
    mut v_a_5177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5183_: u8 = 0;
    let mut v_snd_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: u8 = 0;
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5176_) == 0 {
                    v___x_5178_ = l_List_reverse___redArg(v_a_5177_);
                    return v___x_5178_;
                } else {
                    v_head_5179_ = lean_ctor_get(v_a_5176_, 0);
                    v_tail_5180_ = lean_ctor_get(v_a_5176_, 1);
                    v_isSharedCheck_5191_ = (!lean_is_exclusive(v_a_5176_)) as u8;
                    if v_isSharedCheck_5191_ == 0 {
                        v___x_5182_ = v_a_5176_;
                        v_isShared_5183_ = v_isSharedCheck_5191_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5180_);
                        lean_inc(v_head_5179_);
                        lean_dec(v_a_5176_);
                        v___x_5182_ = lean_box(0);
                        v_isShared_5183_ = v_isSharedCheck_5191_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5184_ = lean_ctor_get(v_head_5179_, 1);
                v___x_5185_ = l_List_isEmpty___redArg(v_snd_5184_);
                if v___x_5185_ == 0 {
                    lean_del_object(v___x_5182_);
                    lean_dec(v_head_5179_);
                    v_a_5176_ = v_tail_5180_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_5183_ == 0 {
                        lean_ctor_set(v___x_5182_, 1, v_a_5177_);
                        v___x_5188_ = v___x_5182_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5190_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_head_5179_);
                        lean_ctor_set(v_reuseFailAlloc_5190_, 1, v_a_5177_);
                        v___x_5188_ = v_reuseFailAlloc_5190_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_5176_ = v_tail_5180_;
                v_a_5177_ = v___x_5188_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(
    mut v_a_5192_: *mut LeanObject,
    mut v_a_5193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5199_: u8 = 0;
    let mut v_fst_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5192_) == 0 {
                    v___x_5194_ = l_List_reverse___redArg(v_a_5193_);
                    return v___x_5194_;
                } else {
                    v_head_5195_ = lean_ctor_get(v_a_5192_, 0);
                    v_tail_5196_ = lean_ctor_get(v_a_5192_, 1);
                    v_isSharedCheck_5205_ = (!lean_is_exclusive(v_a_5192_)) as u8;
                    if v_isSharedCheck_5205_ == 0 {
                        v___x_5198_ = v_a_5192_;
                        v_isShared_5199_ = v_isSharedCheck_5205_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5196_);
                        lean_inc(v_head_5195_);
                        lean_dec(v_a_5192_);
                        v___x_5198_ = lean_box(0);
                        v_isShared_5199_ = v_isSharedCheck_5205_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5200_ = lean_ctor_get(v_head_5195_, 0);
                lean_inc(v_fst_5200_);
                lean_dec(v_head_5195_);
                if v_isShared_5199_ == 0 {
                    lean_ctor_set(v___x_5198_, 1, v_a_5193_);
                    lean_ctor_set(v___x_5198_, 0, v_fst_5200_);
                    v___x_5202_ = v___x_5198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5204_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_fst_5200_);
                    lean_ctor_set(v_reuseFailAlloc_5204_, 1, v_a_5193_);
                    v___x_5202_ = v_reuseFailAlloc_5204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5192_ = v_tail_5196_;
                v_a_5193_ = v___x_5202_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(
    mut v_msg_5206_: *mut LeanObject,
    mut v___y_5207_: *mut LeanObject,
    mut v___y_5208_: *mut LeanObject,
    mut v___y_5209_: *mut LeanObject,
    mut v___y_5210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5217_: u8 = 0;
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5212_ = lean_ctor_get(v___y_5209_, 5);
                v___x_5213_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14_spec__18(v_msg_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_);
                v_a_5214_ = lean_ctor_get(v___x_5213_, 0);
                v_isSharedCheck_5222_ = (!lean_is_exclusive(v___x_5213_)) as u8;
                if v_isSharedCheck_5222_ == 0 {
                    v___x_5216_ = v___x_5213_;
                    v_isShared_5217_ = v_isSharedCheck_5222_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5214_);
                    lean_dec(v___x_5213_);
                    v___x_5216_ = lean_box(0);
                    v_isShared_5217_ = v_isSharedCheck_5222_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5212_);
                v___x_5218_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5218_, 0, v_ref_5212_);
                lean_ctor_set(v___x_5218_, 1, v_a_5214_);
                if v_isShared_5217_ == 0 {
                    lean_ctor_set_tag(v___x_5216_, 1);
                    lean_ctor_set(v___x_5216_, 0, v___x_5218_);
                    v___x_5220_ = v___x_5216_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5221_, 0, v___x_5218_);
                    v___x_5220_ = v_reuseFailAlloc_5221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg___boxed(
    mut v_msg_5223_: *mut LeanObject,
    mut v___y_5224_: *mut LeanObject,
    mut v___y_5225_: *mut LeanObject,
    mut v___y_5226_: *mut LeanObject,
    mut v___y_5227_: *mut LeanObject,
    mut v___y_5228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5229_: *mut LeanObject = core::ptr::null_mut();
    v_res_5229_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_);
    lean_dec(v___y_5227_);
    lean_dec_ref(v___y_5226_);
    lean_dec(v___y_5225_);
    lean_dec_ref(v___y_5224_);
    return v_res_5229_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(
    mut v_ref_5230_: *mut LeanObject,
    mut v_msg_5231_: *mut LeanObject,
    mut v___y_5232_: *mut LeanObject,
    mut v___y_5233_: *mut LeanObject,
    mut v___y_5234_: *mut LeanObject,
    mut v___y_5235_: *mut LeanObject,
    mut v___y_5236_: *mut LeanObject,
    mut v___y_5237_: *mut LeanObject,
    mut v___y_5238_: *mut LeanObject,
    mut v___y_5239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5253_: u8 = 0;
    let mut v_cancelTk_x3f_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5255_: u8 = 0;
    let mut v_inheritedTraceOptions_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_5241_ = lean_ctor_get(v___y_5238_, 0);
    v_fileMap_5242_ = lean_ctor_get(v___y_5238_, 1);
    v_options_5243_ = lean_ctor_get(v___y_5238_, 2);
    v_currRecDepth_5244_ = lean_ctor_get(v___y_5238_, 3);
    v_maxRecDepth_5245_ = lean_ctor_get(v___y_5238_, 4);
    v_ref_5246_ = lean_ctor_get(v___y_5238_, 5);
    v_currNamespace_5247_ = lean_ctor_get(v___y_5238_, 6);
    v_openDecls_5248_ = lean_ctor_get(v___y_5238_, 7);
    v_initHeartbeats_5249_ = lean_ctor_get(v___y_5238_, 8);
    v_maxHeartbeats_5250_ = lean_ctor_get(v___y_5238_, 9);
    v_quotContext_5251_ = lean_ctor_get(v___y_5238_, 10);
    v_currMacroScope_5252_ = lean_ctor_get(v___y_5238_, 11);
    v_diag_5253_ = lean_ctor_get_uint8(
        v___y_5238_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5254_ = lean_ctor_get(v___y_5238_, 12);
    v_suppressElabErrors_5255_ = lean_ctor_get_uint8(
        v___y_5238_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5256_ = lean_ctor_get(v___y_5238_, 13);
    v_ref_5257_ = l_Lean_replaceRef(v_ref_5230_, v_ref_5246_);
    lean_inc_ref(v_inheritedTraceOptions_5256_);
    lean_inc(v_cancelTk_x3f_5254_);
    lean_inc(v_currMacroScope_5252_);
    lean_inc(v_quotContext_5251_);
    lean_inc(v_maxHeartbeats_5250_);
    lean_inc(v_initHeartbeats_5249_);
    lean_inc(v_openDecls_5248_);
    lean_inc(v_currNamespace_5247_);
    lean_inc(v_maxRecDepth_5245_);
    lean_inc(v_currRecDepth_5244_);
    lean_inc_ref(v_options_5243_);
    lean_inc_ref(v_fileMap_5242_);
    lean_inc_ref(v_fileName_5241_);
    v___x_5258_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_5258_, 0, v_fileName_5241_);
    lean_ctor_set(v___x_5258_, 1, v_fileMap_5242_);
    lean_ctor_set(v___x_5258_, 2, v_options_5243_);
    lean_ctor_set(v___x_5258_, 3, v_currRecDepth_5244_);
    lean_ctor_set(v___x_5258_, 4, v_maxRecDepth_5245_);
    lean_ctor_set(v___x_5258_, 5, v_ref_5257_);
    lean_ctor_set(v___x_5258_, 6, v_currNamespace_5247_);
    lean_ctor_set(v___x_5258_, 7, v_openDecls_5248_);
    lean_ctor_set(v___x_5258_, 8, v_initHeartbeats_5249_);
    lean_ctor_set(v___x_5258_, 9, v_maxHeartbeats_5250_);
    lean_ctor_set(v___x_5258_, 10, v_quotContext_5251_);
    lean_ctor_set(v___x_5258_, 11, v_currMacroScope_5252_);
    lean_ctor_set(v___x_5258_, 12, v_cancelTk_x3f_5254_);
    lean_ctor_set(v___x_5258_, 13, v_inheritedTraceOptions_5256_);
    lean_ctor_set_uint8(
        v___x_5258_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_5253_,
    );
    lean_ctor_set_uint8(
        v___x_5258_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5255_,
    );
    v___x_5259_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_5231_, v___y_5236_, v___y_5237_, v___x_5258_, v___y_5239_);
    lean_dec_ref_known(v___x_5258_, 14);
    return v___x_5259_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg___boxed(
    mut v_ref_5260_: *mut LeanObject,
    mut v_msg_5261_: *mut LeanObject,
    mut v___y_5262_: *mut LeanObject,
    mut v___y_5263_: *mut LeanObject,
    mut v___y_5264_: *mut LeanObject,
    mut v___y_5265_: *mut LeanObject,
    mut v___y_5266_: *mut LeanObject,
    mut v___y_5267_: *mut LeanObject,
    mut v___y_5268_: *mut LeanObject,
    mut v___y_5269_: *mut LeanObject,
    mut v___y_5270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5271_: *mut LeanObject = core::ptr::null_mut();
    v_res_5271_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_5260_, v_msg_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
    lean_dec(v___y_5269_);
    lean_dec_ref(v___y_5268_);
    lean_dec(v___y_5267_);
    lean_dec_ref(v___y_5266_);
    lean_dec(v___y_5265_);
    lean_dec_ref(v___y_5264_);
    lean_dec(v___y_5263_);
    lean_dec_ref(v___y_5262_);
    lean_dec(v_ref_5260_);
    return v_res_5271_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    v___x_5272_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5272_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    v___x_5273_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__0);
    v___x_5274_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5274_, 0, v___x_5273_);
    return v___x_5274_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    v___x_5275_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
    v___x_5276_ = lean_unsigned_to_nat(0);
    v___x_5277_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_5277_, 0, v___x_5276_);
    lean_ctor_set(v___x_5277_, 1, v___x_5276_);
    lean_ctor_set(v___x_5277_, 2, v___x_5276_);
    lean_ctor_set(v___x_5277_, 3, v___x_5276_);
    lean_ctor_set(v___x_5277_, 4, v___x_5275_);
    lean_ctor_set(v___x_5277_, 5, v___x_5275_);
    lean_ctor_set(v___x_5277_, 6, v___x_5275_);
    lean_ctor_set(v___x_5277_, 7, v___x_5275_);
    lean_ctor_set(v___x_5277_, 8, v___x_5275_);
    lean_ctor_set(v___x_5277_, 9, v___x_5275_);
    return v___x_5277_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    v___x_5278_ = lean_unsigned_to_nat(32);
    v___x_5279_ = lean_mk_empty_array_with_capacity(v___x_5278_);
    v___x_5280_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5280_, 0, v___x_5279_);
    return v___x_5280_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_5281_: usize = 0;
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    v___x_5281_ = 5usize;
    v___x_5282_ = lean_unsigned_to_nat(0);
    v___x_5283_ = lean_unsigned_to_nat(32);
    v___x_5284_ = lean_mk_empty_array_with_capacity(v___x_5283_);
    v___x_5285_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__3);
    v___x_5286_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_5286_, 0, v___x_5285_);
    lean_ctor_set(v___x_5286_, 1, v___x_5284_);
    lean_ctor_set(v___x_5286_, 2, v___x_5282_);
    lean_ctor_set(v___x_5286_, 3, v___x_5282_);
    lean_ctor_set_usize(v___x_5286_, 4, v___x_5281_);
    return v___x_5286_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    v___x_5287_ = lean_box(1);
    v___x_5288_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__4);
    v___x_5289_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__1);
    v___x_5290_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_5290_, 0, v___x_5289_);
    lean_ctor_set(v___x_5290_, 1, v___x_5288_);
    lean_ctor_set(v___x_5290_, 2, v___x_5287_);
    return v___x_5290_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    v___x_5292_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__6;
    v___x_5293_ = l_Lean_stringToMessageData(v___x_5292_);
    return v___x_5293_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    v___x_5295_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__8;
    v___x_5296_ = l_Lean_stringToMessageData(v___x_5295_);
    return v___x_5296_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    v___x_5298_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__10;
    v___x_5299_ = l_Lean_stringToMessageData(v___x_5298_);
    return v___x_5299_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    v___x_5301_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__12;
    v___x_5302_ = l_Lean_stringToMessageData(v___x_5301_);
    return v___x_5302_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    v___x_5304_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__14;
    v___x_5305_ = l_Lean_stringToMessageData(v___x_5304_);
    return v___x_5305_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    v___x_5307_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__16;
    v___x_5308_ = l_Lean_stringToMessageData(v___x_5307_);
    return v___x_5308_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    v___x_5310_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__18;
    v___x_5311_ = l_Lean_stringToMessageData(v___x_5310_);
    return v___x_5311_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(
    mut v_msg_5312_: *mut LeanObject,
    mut v_declHint_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: u8 = 0;
    let mut v_isExporting_5319_: u8 = 0;
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: u8 = 0;
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5341_: u8 = 0;
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: u8 = 0;
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5373_: u8 = 0;
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5316_ = lean_st_ref_get(v___y_5314_);
                v_env_5317_ = lean_ctor_get(v___x_5316_, 0);
                lean_inc_ref(v_env_5317_);
                lean_dec(v___x_5316_);
                v___x_5318_ = l_Lean_Name_isAnonymous(v_declHint_5313_);
                if v___x_5318_ == 0 {
                    v_isExporting_5319_ = lean_ctor_get_uint8(
                        v_env_5317_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5319_ == 0 {
                        lean_dec_ref(v_env_5317_);
                        lean_dec(v_declHint_5313_);
                        v___x_5320_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5320_, 0, v_msg_5312_);
                        return v___x_5320_;
                    } else {
                        lean_inc_ref(v_env_5317_);
                        v___x_5321_ = l_Lean_Environment_setExporting(v_env_5317_, v___x_5318_);
                        lean_inc(v_declHint_5313_);
                        lean_inc_ref(v___x_5321_);
                        v___x_5322_ = l_Lean_Environment_contains(
                            v___x_5321_,
                            v_declHint_5313_,
                            v_isExporting_5319_,
                        );
                        if v___x_5322_ == 0 {
                            lean_dec_ref(v___x_5321_);
                            lean_dec_ref(v_env_5317_);
                            lean_dec(v_declHint_5313_);
                            v___x_5323_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5323_, 0, v_msg_5312_);
                            return v___x_5323_;
                        } else {
                            v___x_5324_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__2);
                            v___x_5325_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__5);
                            v___x_5326_ = l_Lean_Options_empty;
                            v___x_5327_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_5327_, 0, v___x_5321_);
                            lean_ctor_set(v___x_5327_, 1, v___x_5324_);
                            lean_ctor_set(v___x_5327_, 2, v___x_5325_);
                            lean_ctor_set(v___x_5327_, 3, v___x_5326_);
                            lean_inc(v_declHint_5313_);
                            v___x_5328_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5313_, v___x_5318_);
                            v_c_5329_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_5329_, 0, v___x_5327_);
                            lean_ctor_set(v_c_5329_, 1, v___x_5328_);
                            v___x_5330_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5317_,
                                v_declHint_5313_,
                            );
                            if lean_obj_tag(v___x_5330_) == 0 {
                                lean_dec_ref(v_env_5317_);
                                lean_dec(v_declHint_5313_);
                                v___x_5331_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
                                v___x_5332_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5332_, 0, v___x_5331_);
                                lean_ctor_set(v___x_5332_, 1, v_c_5329_);
                                v___x_5333_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__9);
                                v___x_5334_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5334_, 0, v___x_5332_);
                                lean_ctor_set(v___x_5334_, 1, v___x_5333_);
                                v___x_5335_ = l_Lean_MessageData_note(v___x_5334_);
                                v___x_5336_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5336_, 0, v_msg_5312_);
                                lean_ctor_set(v___x_5336_, 1, v___x_5335_);
                                v___x_5337_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_5337_, 0, v___x_5336_);
                                return v___x_5337_;
                            } else {
                                v_val_5338_ = lean_ctor_get(v___x_5330_, 0);
                                v_isSharedCheck_5373_ = (!lean_is_exclusive(v___x_5330_)) as u8;
                                if v_isSharedCheck_5373_ == 0 {
                                    v___x_5340_ = v___x_5330_;
                                    v_isShared_5341_ = v_isSharedCheck_5373_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_5338_);
                                    lean_dec(v___x_5330_);
                                    v___x_5340_ = lean_box(0);
                                    v_isShared_5341_ = v_isSharedCheck_5373_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_5317_);
                    lean_dec(v_declHint_5313_);
                    v___x_5374_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5374_, 0, v_msg_5312_);
                    return v___x_5374_;
                }
            }
            1 => {
                v___x_5342_ = lean_box(0);
                v___x_5343_ = l_Lean_Environment_header(v_env_5317_);
                lean_dec_ref(v_env_5317_);
                v___x_5344_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5343_);
                v_mod_5345_ = lean_array_get(v___x_5342_, v___x_5344_, v_val_5338_);
                lean_dec(v_val_5338_);
                lean_dec_ref(v___x_5344_);
                v___x_5346_ = l_Lean_isPrivateName(v_declHint_5313_);
                lean_dec(v_declHint_5313_);
                if v___x_5346_ == 0 {
                    v___x_5347_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__11);
                    v___x_5348_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5348_, 0, v___x_5347_);
                    lean_ctor_set(v___x_5348_, 1, v_c_5329_);
                    v___x_5349_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__13);
                    v___x_5350_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5350_, 0, v___x_5348_);
                    lean_ctor_set(v___x_5350_, 1, v___x_5349_);
                    v___x_5351_ = l_Lean_MessageData_ofName(v_mod_5345_);
                    v___x_5352_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5352_, 0, v___x_5350_);
                    lean_ctor_set(v___x_5352_, 1, v___x_5351_);
                    v___x_5353_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__15);
                    v___x_5354_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5354_, 0, v___x_5352_);
                    lean_ctor_set(v___x_5354_, 1, v___x_5353_);
                    v___x_5355_ = l_Lean_MessageData_note(v___x_5354_);
                    v___x_5356_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5356_, 0, v_msg_5312_);
                    lean_ctor_set(v___x_5356_, 1, v___x_5355_);
                    if v_isShared_5341_ == 0 {
                        lean_ctor_set_tag(v___x_5340_, 0);
                        lean_ctor_set(v___x_5340_, 0, v___x_5356_);
                        v___x_5358_ = v___x_5340_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5359_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5356_);
                        v___x_5358_ = v_reuseFailAlloc_5359_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5360_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__7);
                    v___x_5361_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5361_, 0, v___x_5360_);
                    lean_ctor_set(v___x_5361_, 1, v_c_5329_);
                    v___x_5362_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__17);
                    v___x_5363_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5363_, 0, v___x_5361_);
                    lean_ctor_set(v___x_5363_, 1, v___x_5362_);
                    v___x_5364_ = l_Lean_MessageData_ofName(v_mod_5345_);
                    v___x_5365_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5365_, 0, v___x_5363_);
                    lean_ctor_set(v___x_5365_, 1, v___x_5364_);
                    v___x_5366_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___closed__19);
                    v___x_5367_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5367_, 0, v___x_5365_);
                    lean_ctor_set(v___x_5367_, 1, v___x_5366_);
                    v___x_5368_ = l_Lean_MessageData_note(v___x_5367_);
                    v___x_5369_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5369_, 0, v_msg_5312_);
                    lean_ctor_set(v___x_5369_, 1, v___x_5368_);
                    if v_isShared_5341_ == 0 {
                        lean_ctor_set_tag(v___x_5340_, 0);
                        lean_ctor_set(v___x_5340_, 0, v___x_5369_);
                        v___x_5371_ = v___x_5340_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5369_);
                        v___x_5371_ = v_reuseFailAlloc_5372_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5358_;
            }
            3 => {
                return v___x_5371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg___boxed(
    mut v_msg_5375_: *mut LeanObject,
    mut v_declHint_5376_: *mut LeanObject,
    mut v___y_5377_: *mut LeanObject,
    mut v___y_5378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5379_: *mut LeanObject = core::ptr::null_mut();
    v_res_5379_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_5375_, v_declHint_5376_, v___y_5377_);
    lean_dec(v___y_5377_);
    return v_res_5379_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(
    mut v_msg_5380_: *mut LeanObject,
    mut v_declHint_5381_: *mut LeanObject,
    mut v___y_5382_: *mut LeanObject,
    mut v___y_5383_: *mut LeanObject,
    mut v___y_5384_: *mut LeanObject,
    mut v___y_5385_: *mut LeanObject,
    mut v___y_5386_: *mut LeanObject,
    mut v___y_5387_: *mut LeanObject,
    mut v___y_5388_: *mut LeanObject,
    mut v___y_5389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5395_: u8 = 0;
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5391_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_5380_, v_declHint_5381_, v___y_5389_);
                v_a_5392_ = lean_ctor_get(v___x_5391_, 0);
                v_isSharedCheck_5401_ = (!lean_is_exclusive(v___x_5391_)) as u8;
                if v_isSharedCheck_5401_ == 0 {
                    v___x_5394_ = v___x_5391_;
                    v_isShared_5395_ = v_isSharedCheck_5401_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5392_);
                    lean_dec(v___x_5391_);
                    v___x_5394_ = lean_box(0);
                    v_isShared_5395_ = v_isSharedCheck_5401_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5396_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5397_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_5397_, 0, v___x_5396_);
                lean_ctor_set(v___x_5397_, 1, v_a_5392_);
                if v_isShared_5395_ == 0 {
                    lean_ctor_set(v___x_5394_, 0, v___x_5397_);
                    v___x_5399_ = v___x_5394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5400_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5400_, 0, v___x_5397_);
                    v___x_5399_ = v_reuseFailAlloc_5400_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19___boxed(
    mut v_msg_5402_: *mut LeanObject,
    mut v_declHint_5403_: *mut LeanObject,
    mut v___y_5404_: *mut LeanObject,
    mut v___y_5405_: *mut LeanObject,
    mut v___y_5406_: *mut LeanObject,
    mut v___y_5407_: *mut LeanObject,
    mut v___y_5408_: *mut LeanObject,
    mut v___y_5409_: *mut LeanObject,
    mut v___y_5410_: *mut LeanObject,
    mut v___y_5411_: *mut LeanObject,
    mut v___y_5412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5413_: *mut LeanObject = core::ptr::null_mut();
    v_res_5413_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_5402_, v_declHint_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_);
    lean_dec(v___y_5411_);
    lean_dec_ref(v___y_5410_);
    lean_dec(v___y_5409_);
    lean_dec_ref(v___y_5408_);
    lean_dec(v___y_5407_);
    lean_dec_ref(v___y_5406_);
    lean_dec(v___y_5405_);
    lean_dec_ref(v___y_5404_);
    return v_res_5413_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(
    mut v_ref_5414_: *mut LeanObject,
    mut v_msg_5415_: *mut LeanObject,
    mut v_declHint_5416_: *mut LeanObject,
    mut v___y_5417_: *mut LeanObject,
    mut v___y_5418_: *mut LeanObject,
    mut v___y_5419_: *mut LeanObject,
    mut v___y_5420_: *mut LeanObject,
    mut v___y_5421_: *mut LeanObject,
    mut v___y_5422_: *mut LeanObject,
    mut v___y_5423_: *mut LeanObject,
    mut v___y_5424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    v___x_5426_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19(v_msg_5415_, v_declHint_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_);
    v_a_5427_ = lean_ctor_get(v___x_5426_, 0);
    lean_inc(v_a_5427_);
    lean_dec_ref(v___x_5426_);
    v___x_5428_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_5414_, v_a_5427_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_);
    return v___x_5428_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg___boxed(
    mut v_ref_5429_: *mut LeanObject,
    mut v_msg_5430_: *mut LeanObject,
    mut v_declHint_5431_: *mut LeanObject,
    mut v___y_5432_: *mut LeanObject,
    mut v___y_5433_: *mut LeanObject,
    mut v___y_5434_: *mut LeanObject,
    mut v___y_5435_: *mut LeanObject,
    mut v___y_5436_: *mut LeanObject,
    mut v___y_5437_: *mut LeanObject,
    mut v___y_5438_: *mut LeanObject,
    mut v___y_5439_: *mut LeanObject,
    mut v___y_5440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5441_: *mut LeanObject = core::ptr::null_mut();
    v_res_5441_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_5429_, v_msg_5430_, v_declHint_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_);
    lean_dec(v___y_5439_);
    lean_dec_ref(v___y_5438_);
    lean_dec(v___y_5437_);
    lean_dec_ref(v___y_5436_);
    lean_dec(v___y_5435_);
    lean_dec_ref(v___y_5434_);
    lean_dec(v___y_5433_);
    lean_dec_ref(v___y_5432_);
    lean_dec(v_ref_5429_);
    return v_res_5441_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    v___x_5443_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__0;
    v___x_5444_ = l_Lean_stringToMessageData(v___x_5443_);
    return v___x_5444_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    v___x_5446_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__2;
    v___x_5447_ = l_Lean_stringToMessageData(v___x_5446_);
    return v___x_5447_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(
    mut v_ref_5448_: *mut LeanObject,
    mut v_constName_5449_: *mut LeanObject,
    mut v___y_5450_: *mut LeanObject,
    mut v___y_5451_: *mut LeanObject,
    mut v___y_5452_: *mut LeanObject,
    mut v___y_5453_: *mut LeanObject,
    mut v___y_5454_: *mut LeanObject,
    mut v___y_5455_: *mut LeanObject,
    mut v___y_5456_: *mut LeanObject,
    mut v___y_5457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: u8 = 0;
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    v___x_5459_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__1);
    v___x_5460_ = 0;
    lean_inc(v_constName_5449_);
    v___x_5461_ = l_Lean_MessageData_ofConstName(v_constName_5449_, v___x_5460_);
    v___x_5462_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5462_, 0, v___x_5459_);
    lean_ctor_set(v___x_5462_, 1, v___x_5461_);
    v___x_5463_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___closed__3);
    v___x_5464_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5464_, 0, v___x_5462_);
    lean_ctor_set(v___x_5464_, 1, v___x_5463_);
    v___x_5465_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_5448_, v___x_5464_, v_constName_5449_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
    return v___x_5465_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg___boxed(
    mut v_ref_5466_: *mut LeanObject,
    mut v_constName_5467_: *mut LeanObject,
    mut v___y_5468_: *mut LeanObject,
    mut v___y_5469_: *mut LeanObject,
    mut v___y_5470_: *mut LeanObject,
    mut v___y_5471_: *mut LeanObject,
    mut v___y_5472_: *mut LeanObject,
    mut v___y_5473_: *mut LeanObject,
    mut v___y_5474_: *mut LeanObject,
    mut v___y_5475_: *mut LeanObject,
    mut v___y_5476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5477_: *mut LeanObject = core::ptr::null_mut();
    v_res_5477_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_5466_, v_constName_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
    lean_dec(v___y_5475_);
    lean_dec_ref(v___y_5474_);
    lean_dec(v___y_5473_);
    lean_dec_ref(v___y_5472_);
    lean_dec(v___y_5471_);
    lean_dec_ref(v___y_5470_);
    lean_dec(v___y_5469_);
    lean_dec_ref(v___y_5468_);
    lean_dec(v_ref_5466_);
    return v_res_5477_;
}
pub unsafe fn l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(
    mut v_n_5478_: *mut LeanObject,
    mut v_cs_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
    mut v___y_5484_: *mut LeanObject,
    mut v___y_5485_: *mut LeanObject,
    mut v___y_5486_: *mut LeanObject,
    mut v___y_5487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cs_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: u8 = 0;
    let mut v_ref_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5500_: u8 = 0;
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5489_ = lean_box(0);
                v_cs_5490_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__8(v_cs_5479_, v___x_5489_);
                v___x_5494_ = l_List_isEmpty___redArg(v_cs_5490_);
                if v___x_5494_ == 0 {
                    lean_dec(v_n_5478_);
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_cs_5490_);
                    v_ref_5495_ = lean_ctor_get(v___y_5486_, 5);
                    v___x_5496_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_5495_, v_n_5478_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_);
                    v_a_5497_ = lean_ctor_get(v___x_5496_, 0);
                    v_isSharedCheck_5504_ = (!lean_is_exclusive(v___x_5496_)) as u8;
                    if v_isSharedCheck_5504_ == 0 {
                        v___x_5499_ = v___x_5496_;
                        v_isShared_5500_ = v_isSharedCheck_5504_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5497_);
                        lean_dec(v___x_5496_);
                        v___x_5499_ = lean_box(0);
                        v_isShared_5500_ = v_isSharedCheck_5504_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5492_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__9(v_cs_5490_, v___x_5489_);
                v___x_5493_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5493_, 0, v___x_5492_);
                return v___x_5493_;
            }
            2 => {
                if v_isShared_5500_ == 0 {
                    v___x_5502_ = v___x_5499_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5503_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5503_, 0, v_a_5497_);
                    v___x_5502_ = v_reuseFailAlloc_5503_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3___boxed(
    mut v_n_5505_: *mut LeanObject,
    mut v_cs_5506_: *mut LeanObject,
    mut v___y_5507_: *mut LeanObject,
    mut v___y_5508_: *mut LeanObject,
    mut v___y_5509_: *mut LeanObject,
    mut v___y_5510_: *mut LeanObject,
    mut v___y_5511_: *mut LeanObject,
    mut v___y_5512_: *mut LeanObject,
    mut v___y_5513_: *mut LeanObject,
    mut v___y_5514_: *mut LeanObject,
    mut v___y_5515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5516_: *mut LeanObject = core::ptr::null_mut();
    v_res_5516_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_5505_, v_cs_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_);
    lean_dec(v___y_5514_);
    lean_dec_ref(v___y_5513_);
    lean_dec(v___y_5512_);
    lean_dec_ref(v___y_5511_);
    lean_dec(v___y_5510_);
    lean_dec_ref(v___y_5509_);
    lean_dec(v___y_5508_);
    lean_dec_ref(v___y_5507_);
    return v_res_5516_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(
    mut v_n_5517_: *mut LeanObject,
    mut v___y_5518_: *mut LeanObject,
    mut v___y_5519_: *mut LeanObject,
    mut v___y_5520_: *mut LeanObject,
    mut v___y_5521_: *mut LeanObject,
    mut v___y_5522_: *mut LeanObject,
    mut v___y_5523_: *mut LeanObject,
    mut v___y_5524_: *mut LeanObject,
    mut v___y_5525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5527_: u8 = 0;
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5534_: u8 = 0;
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5527_ = 1;
                lean_inc(v_n_5517_);
                v___x_5528_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2(v_n_5517_, v___x_5527_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
                if lean_obj_tag(v___x_5528_) == 0 {
                    v_a_5529_ = lean_ctor_get(v___x_5528_, 0);
                    lean_inc(v_a_5529_);
                    lean_dec_ref_known(v___x_5528_, 1);
                    v___x_5530_ = l_Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3(v_n_5517_, v_a_5529_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
                    return v___x_5530_;
                } else {
                    lean_dec(v_n_5517_);
                    v_a_5531_ = lean_ctor_get(v___x_5528_, 0);
                    v_isSharedCheck_5538_ = (!lean_is_exclusive(v___x_5528_)) as u8;
                    if v_isSharedCheck_5538_ == 0 {
                        v___x_5533_ = v___x_5528_;
                        v_isShared_5534_ = v_isSharedCheck_5538_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5531_);
                        lean_dec(v___x_5528_);
                        v___x_5533_ = lean_box(0);
                        v_isShared_5534_ = v_isSharedCheck_5538_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5534_ == 0 {
                    v___x_5536_ = v___x_5533_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5537_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_a_5531_);
                    v___x_5536_ = v_reuseFailAlloc_5537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1___boxed(
    mut v_n_5539_: *mut LeanObject,
    mut v___y_5540_: *mut LeanObject,
    mut v___y_5541_: *mut LeanObject,
    mut v___y_5542_: *mut LeanObject,
    mut v___y_5543_: *mut LeanObject,
    mut v___y_5544_: *mut LeanObject,
    mut v___y_5545_: *mut LeanObject,
    mut v___y_5546_: *mut LeanObject,
    mut v___y_5547_: *mut LeanObject,
    mut v___y_5548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5549_: *mut LeanObject = core::ptr::null_mut();
    v_res_5549_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1(v_n_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_);
    lean_dec(v___y_5547_);
    lean_dec_ref(v___y_5546_);
    lean_dec(v___y_5545_);
    lean_dec_ref(v___y_5544_);
    lean_dec(v___y_5543_);
    lean_dec_ref(v___y_5542_);
    lean_dec(v___y_5541_);
    lean_dec_ref(v___y_5540_);
    return v_res_5549_;
}
pub unsafe fn l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(
    mut v_a_5550_: *mut LeanObject,
    mut v_a_5551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5550_) == 0 {
                    v___x_5552_ = lean_array_to_list(v_a_5551_);
                    return v___x_5552_;
                } else {
                    v_head_5553_ = lean_ctor_get(v_a_5550_, 0);
                    if lean_obj_tag(v_head_5553_) == 1 {
                        v_fields_5554_ = lean_ctor_get(v_head_5553_, 1);
                        if lean_obj_tag(v_fields_5554_) == 0 {
                            lean_inc_ref(v_head_5553_);
                            v_tail_5555_ = lean_ctor_get(v_a_5550_, 1);
                            lean_inc(v_tail_5555_);
                            lean_dec_ref_known(v_a_5550_, 2);
                            v_n_5556_ = lean_ctor_get(v_head_5553_, 0);
                            lean_inc(v_n_5556_);
                            lean_dec_ref_known(v_head_5553_, 2);
                            v___x_5557_ = lean_array_push(v_a_5551_, v_n_5556_);
                            v_a_5550_ = v_tail_5555_;
                            v_a_5551_ = v___x_5557_;
                            state = 0;
                            continue;
                        } else {
                            v_tail_5559_ = lean_ctor_get(v_a_5550_, 1);
                            lean_inc(v_tail_5559_);
                            lean_dec_ref_known(v_a_5550_, 2);
                            v_a_5550_ = v_tail_5559_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_tail_5561_ = lean_ctor_get(v_a_5550_, 1);
                        lean_inc(v_tail_5561_);
                        lean_dec_ref_known(v_a_5550_, 2);
                        v_a_5550_ = v_tail_5561_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    v___x_5568_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__2;
    v___x_5569_ = l_Lean_MessageData_ofFormat(v___x_5568_);
    return v___x_5569_;
}
pub unsafe fn l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(
    mut v_stx_5570_: *mut LeanObject,
    mut v_k_5571_: *mut LeanObject,
    mut v___y_5572_: *mut LeanObject,
    mut v___y_5573_: *mut LeanObject,
    mut v___y_5574_: *mut LeanObject,
    mut v___y_5575_: *mut LeanObject,
    mut v___y_5576_: *mut LeanObject,
    mut v___y_5577_: *mut LeanObject,
    mut v___y_5578_: *mut LeanObject,
    mut v___y_5579_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_stx_5570_) == 3 {
        let mut v_val_5581_: *mut LeanObject = core::ptr::null_mut();
        let mut v_preresolved_5582_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pre_5584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5585_: u8 = 0;
        v_val_5581_ = lean_ctor_get(v_stx_5570_, 2);
        lean_inc(v_val_5581_);
        v_preresolved_5582_ = lean_ctor_get(v_stx_5570_, 3);
        v___x_5583_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__0;
        lean_inc(v_preresolved_5582_);
        v_pre_5584_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__5(v_preresolved_5582_, v___x_5583_);
        v___x_5585_ = l_List_isEmpty___redArg(v_pre_5584_);
        if v___x_5585_ == 0 {
            let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_5581_);
            lean_dec_ref_known(v_stx_5570_, 4);
            lean_dec_ref(v_k_5571_);
            v___x_5586_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_5586_, 0, v_pre_5584_);
            return v___x_5586_;
        } else {
            let mut v_fileName_5587_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fileMap_5588_: *mut LeanObject = core::ptr::null_mut();
            let mut v_options_5589_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currRecDepth_5590_: *mut LeanObject = core::ptr::null_mut();
            let mut v_maxRecDepth_5591_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_5592_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currNamespace_5593_: *mut LeanObject = core::ptr::null_mut();
            let mut v_openDecls_5594_: *mut LeanObject = core::ptr::null_mut();
            let mut v_initHeartbeats_5595_: *mut LeanObject = core::ptr::null_mut();
            let mut v_maxHeartbeats_5596_: *mut LeanObject = core::ptr::null_mut();
            let mut v_quotContext_5597_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_5598_: *mut LeanObject = core::ptr::null_mut();
            let mut v_diag_5599_: u8 = 0;
            let mut v_cancelTk_x3f_5600_: *mut LeanObject = core::ptr::null_mut();
            let mut v_suppressElabErrors_5601_: u8 = 0;
            let mut v_inheritedTraceOptions_5602_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_5603_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_pre_5584_);
            v_fileName_5587_ = lean_ctor_get(v___y_5578_, 0);
            v_fileMap_5588_ = lean_ctor_get(v___y_5578_, 1);
            v_options_5589_ = lean_ctor_get(v___y_5578_, 2);
            v_currRecDepth_5590_ = lean_ctor_get(v___y_5578_, 3);
            v_maxRecDepth_5591_ = lean_ctor_get(v___y_5578_, 4);
            v_ref_5592_ = lean_ctor_get(v___y_5578_, 5);
            v_currNamespace_5593_ = lean_ctor_get(v___y_5578_, 6);
            v_openDecls_5594_ = lean_ctor_get(v___y_5578_, 7);
            v_initHeartbeats_5595_ = lean_ctor_get(v___y_5578_, 8);
            v_maxHeartbeats_5596_ = lean_ctor_get(v___y_5578_, 9);
            v_quotContext_5597_ = lean_ctor_get(v___y_5578_, 10);
            v_currMacroScope_5598_ = lean_ctor_get(v___y_5578_, 11);
            v_diag_5599_ = lean_ctor_get_uint8(
                v___y_5578_,
                (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
            );
            v_cancelTk_x3f_5600_ = lean_ctor_get(v___y_5578_, 12);
            v_suppressElabErrors_5601_ = lean_ctor_get_uint8(
                v___y_5578_,
                (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
            );
            v_inheritedTraceOptions_5602_ = lean_ctor_get(v___y_5578_, 13);
            v_ref_5603_ = l_Lean_replaceRef(v_stx_5570_, v_ref_5592_);
            lean_dec_ref_known(v_stx_5570_, 4);
            lean_inc_ref(v_inheritedTraceOptions_5602_);
            lean_inc(v_cancelTk_x3f_5600_);
            lean_inc(v_currMacroScope_5598_);
            lean_inc(v_quotContext_5597_);
            lean_inc(v_maxHeartbeats_5596_);
            lean_inc(v_initHeartbeats_5595_);
            lean_inc(v_openDecls_5594_);
            lean_inc(v_currNamespace_5593_);
            lean_inc(v_maxRecDepth_5591_);
            lean_inc(v_currRecDepth_5590_);
            lean_inc_ref(v_options_5589_);
            lean_inc_ref(v_fileMap_5588_);
            lean_inc_ref(v_fileName_5587_);
            v___x_5604_ = lean_alloc_ctor(0, 14, (2) as u32);
            lean_ctor_set(v___x_5604_, 0, v_fileName_5587_);
            lean_ctor_set(v___x_5604_, 1, v_fileMap_5588_);
            lean_ctor_set(v___x_5604_, 2, v_options_5589_);
            lean_ctor_set(v___x_5604_, 3, v_currRecDepth_5590_);
            lean_ctor_set(v___x_5604_, 4, v_maxRecDepth_5591_);
            lean_ctor_set(v___x_5604_, 5, v_ref_5603_);
            lean_ctor_set(v___x_5604_, 6, v_currNamespace_5593_);
            lean_ctor_set(v___x_5604_, 7, v_openDecls_5594_);
            lean_ctor_set(v___x_5604_, 8, v_initHeartbeats_5595_);
            lean_ctor_set(v___x_5604_, 9, v_maxHeartbeats_5596_);
            lean_ctor_set(v___x_5604_, 10, v_quotContext_5597_);
            lean_ctor_set(v___x_5604_, 11, v_currMacroScope_5598_);
            lean_ctor_set(v___x_5604_, 12, v_cancelTk_x3f_5600_);
            lean_ctor_set(v___x_5604_, 13, v_inheritedTraceOptions_5602_);
            lean_ctor_set_uint8(
                v___x_5604_,
                (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                v_diag_5599_,
            );
            lean_ctor_set_uint8(
                v___x_5604_,
                (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                v_suppressElabErrors_5601_,
            );
            lean_inc(v___y_5579_);
            lean_inc(v___y_5577_);
            lean_inc_ref(v___y_5576_);
            lean_inc(v___y_5575_);
            lean_inc_ref(v___y_5574_);
            lean_inc(v___y_5573_);
            lean_inc_ref(v___y_5572_);
            v___x_5605_ = lean_apply_10(
                v_k_5571_,
                v_val_5581_,
                v___y_5572_,
                v___y_5573_,
                v___y_5574_,
                v___y_5575_,
                v___y_5576_,
                v___y_5577_,
                v___x_5604_,
                v___y_5579_,
                lean_box(0),
            );
            return v___x_5605_;
        }
    } else {
        let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5607_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_5571_);
        v___x_5606_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3_once), _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___closed__3);
        v___x_5607_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_stx_5570_, v___x_5606_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_);
        lean_dec(v_stx_5570_);
        return v___x_5607_;
    }
}
pub unsafe fn l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2___boxed(
    mut v_stx_5608_: *mut LeanObject,
    mut v_k_5609_: *mut LeanObject,
    mut v___y_5610_: *mut LeanObject,
    mut v___y_5611_: *mut LeanObject,
    mut v___y_5612_: *mut LeanObject,
    mut v___y_5613_: *mut LeanObject,
    mut v___y_5614_: *mut LeanObject,
    mut v___y_5615_: *mut LeanObject,
    mut v___y_5616_: *mut LeanObject,
    mut v___y_5617_: *mut LeanObject,
    mut v___y_5618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5619_: *mut LeanObject = core::ptr::null_mut();
    v_res_5619_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_5608_, v_k_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_);
    lean_dec(v___y_5617_);
    lean_dec_ref(v___y_5616_);
    lean_dec(v___y_5615_);
    lean_dec_ref(v___y_5614_);
    lean_dec(v___y_5613_);
    lean_dec_ref(v___y_5612_);
    lean_dec(v___y_5611_);
    lean_dec_ref(v___y_5610_);
    return v_res_5619_;
}
pub unsafe fn l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(
    mut v_stx_5621_: *mut LeanObject,
    mut v___y_5622_: *mut LeanObject,
    mut v___y_5623_: *mut LeanObject,
    mut v___y_5624_: *mut LeanObject,
    mut v___y_5625_: *mut LeanObject,
    mut v___y_5626_: *mut LeanObject,
    mut v___y_5627_: *mut LeanObject,
    mut v___y_5628_: *mut LeanObject,
    mut v___y_5629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    v___x_5631_ =
        l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___closed__0;
    v___x_5632_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2(v_stx_5621_, v___x_5631_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_);
    return v___x_5632_;
}
pub unsafe fn l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1___boxed(
    mut v_stx_5633_: *mut LeanObject,
    mut v___y_5634_: *mut LeanObject,
    mut v___y_5635_: *mut LeanObject,
    mut v___y_5636_: *mut LeanObject,
    mut v___y_5637_: *mut LeanObject,
    mut v___y_5638_: *mut LeanObject,
    mut v___y_5639_: *mut LeanObject,
    mut v___y_5640_: *mut LeanObject,
    mut v___y_5641_: *mut LeanObject,
    mut v___y_5642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5643_: *mut LeanObject = core::ptr::null_mut();
    v_res_5643_ = l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(
        v_stx_5633_,
        v___y_5634_,
        v___y_5635_,
        v___y_5636_,
        v___y_5637_,
        v___y_5638_,
        v___y_5639_,
        v___y_5640_,
        v___y_5641_,
    );
    lean_dec(v___y_5641_);
    lean_dec_ref(v___y_5640_);
    lean_dec(v___y_5639_);
    lean_dec_ref(v___y_5638_);
    lean_dec(v___y_5637_);
    lean_dec_ref(v___y_5636_);
    lean_dec(v___y_5635_);
    lean_dec_ref(v___y_5634_);
    return v_res_5643_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(
    mut v_as_5644_: *mut LeanObject,
    mut v_sz_5645_: usize,
    mut v_i_5646_: usize,
    mut v_b_5647_: *mut LeanObject,
    mut v___y_5648_: *mut LeanObject,
    mut v___y_5649_: *mut LeanObject,
    mut v___y_5650_: *mut LeanObject,
    mut v___y_5651_: *mut LeanObject,
    mut v___y_5652_: *mut LeanObject,
    mut v___y_5653_: *mut LeanObject,
    mut v___y_5654_: *mut LeanObject,
    mut v___y_5655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5657_: u8 = 0;
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: usize = 0;
    let mut v___x_5667_: usize = 0;
    let mut v_a_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5672_: u8 = 0;
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5657_ = lean_usize_dec_lt(v_i_5646_, v_sz_5645_);
                if v___x_5657_ == 0 {
                    v___x_5658_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5658_, 0, v_b_5647_);
                    return v___x_5658_;
                } else {
                    v_a_5659_ = lean_array_uget_borrowed(v_as_5644_, v_i_5646_);
                    v_name_5660_ = lean_ctor_get(v_a_5659_, 0);
                    lean_inc(v_name_5660_);
                    v___x_5661_ = lean_mk_syntax_ident(v_name_5660_);
                    lean_inc(v___x_5661_);
                    v___x_5662_ =
                        l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(
                            v___x_5661_,
                            v___y_5648_,
                            v___y_5649_,
                            v___y_5650_,
                            v___y_5651_,
                            v___y_5652_,
                            v___y_5653_,
                            v___y_5654_,
                            v___y_5655_,
                        );
                    if lean_obj_tag(v___x_5662_) == 0 {
                        v_a_5663_ = lean_ctor_get(v___x_5662_, 0);
                        lean_inc(v_a_5663_);
                        lean_dec_ref_known(v___x_5662_, 1);
                        v___x_5664_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(v___x_5661_, v_a_5663_, v_b_5647_, v___y_5654_);
                        lean_dec(v_a_5663_);
                        lean_dec(v___x_5661_);
                        if lean_obj_tag(v___x_5664_) == 0 {
                            v_a_5665_ = lean_ctor_get(v___x_5664_, 0);
                            lean_inc(v_a_5665_);
                            lean_dec_ref_known(v___x_5664_, 1);
                            v___x_5666_ = 1usize;
                            v___x_5667_ = lean_usize_add(v_i_5646_, v___x_5666_);
                            v_i_5646_ = v___x_5667_;
                            v_b_5647_ = v_a_5665_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_5664_;
                        }
                    } else {
                        lean_dec(v___x_5661_);
                        lean_dec_ref(v_b_5647_);
                        v_a_5669_ = lean_ctor_get(v___x_5662_, 0);
                        v_isSharedCheck_5676_ = (!lean_is_exclusive(v___x_5662_)) as u8;
                        if v_isSharedCheck_5676_ == 0 {
                            v___x_5671_ = v___x_5662_;
                            v_isShared_5672_ = v_isSharedCheck_5676_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5669_);
                            lean_dec(v___x_5662_);
                            v___x_5671_ = lean_box(0);
                            v_isShared_5672_ = v_isSharedCheck_5676_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5672_ == 0 {
                    v___x_5674_ = v___x_5671_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5675_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5669_);
                    v___x_5674_ = v_reuseFailAlloc_5675_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3___boxed(
    mut v_as_5677_: *mut LeanObject,
    mut v_sz_5678_: *mut LeanObject,
    mut v_i_5679_: *mut LeanObject,
    mut v_b_5680_: *mut LeanObject,
    mut v___y_5681_: *mut LeanObject,
    mut v___y_5682_: *mut LeanObject,
    mut v___y_5683_: *mut LeanObject,
    mut v___y_5684_: *mut LeanObject,
    mut v___y_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
    mut v___y_5687_: *mut LeanObject,
    mut v___y_5688_: *mut LeanObject,
    mut v___y_5689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5690_: usize = 0;
    let mut v_i_boxed_5691_: usize = 0;
    let mut v_res_5692_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5690_ = lean_unbox_usize(v_sz_5678_);
    lean_dec(v_sz_5678_);
    v_i_boxed_5691_ = lean_unbox_usize(v_i_5679_);
    lean_dec(v_i_5679_);
    v_res_5692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_as_5677_, v_sz_boxed_5690_, v_i_boxed_5691_, v_b_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_);
    lean_dec(v___y_5688_);
    lean_dec_ref(v___y_5687_);
    lean_dec(v___y_5686_);
    lean_dec_ref(v___y_5685_);
    lean_dec(v___y_5684_);
    lean_dec_ref(v___y_5683_);
    lean_dec(v___y_5682_);
    lean_dec_ref(v___y_5681_);
    lean_dec_ref(v_as_5677_);
    return v_res_5692_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpTrace___lam__2(
    mut v___x_5712_: u8,
    mut v_stx_5713_: *mut LeanObject,
    mut v___x_5714_: u8,
    mut v___x_5715_: *mut LeanObject,
    mut v___x_5716_: *mut LeanObject,
    mut v___x_5717_: *mut LeanObject,
    mut v___f_5718_: *mut LeanObject,
    mut v___y_5719_: *mut LeanObject,
    mut v___y_5720_: *mut LeanObject,
    mut v___y_5721_: *mut LeanObject,
    mut v___y_5722_: *mut LeanObject,
    mut v___y_5723_: *mut LeanObject,
    mut v___y_5724_: *mut LeanObject,
    mut v___y_5725_: *mut LeanObject,
    mut v___y_5726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5753_: u8 = 0;
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: u8 = 0;
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5769_: u8 = 0;
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5773_: u8 = 0;
    let mut v_unused_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5778_: u8 = 0;
    let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5782_: u8 = 0;
    let mut v_reuseFailAlloc_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5787_: u8 = 0;
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5791_: u8 = 0;
    let mut v_isSharedCheck_5792_: u8 = 0;
    let mut v_a_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5796_: u8 = 0;
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5800_: u8 = 0;
    let mut v___y_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5805_: u8 = 0;
    let mut v___y_5806_: u8 = 0;
    let mut v_stxForSuggestion_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: u8 = 0;
    let mut v___x_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocs_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dischargeWrapper_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocs_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dischargeWrapper_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocs_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dischargeWrapper_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5833_: u8 = 0;
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5837_: u8 = 0;
    let mut v___y_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5846_: u8 = 0;
    let mut v___y_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5854_: u8 = 0;
    let mut v___y_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5874_: u8 = 0;
    let mut v___y_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5882_: u8 = 0;
    let mut v___y_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5912_: u8 = 0;
    let mut v___y_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5920_: u8 = 0;
    let mut v___y_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5947_: u8 = 0;
    let mut v___y_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5953_: u8 = 0;
    let mut v___y_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5974_: u8 = 0;
    let mut v___y_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5981_: u8 = 0;
    let mut v___y_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6012_: u8 = 0;
    let mut v___y_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6018_: u8 = 0;
    let mut v___y_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6042_: u8 = 0;
    let mut v___y_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6047_: u8 = 0;
    let mut v___y_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6051_: u8 = 0;
    let mut v_ref_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6068_: u8 = 0;
    let mut v___y_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6071_: u8 = 0;
    let mut v___y_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxForExecution_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: u8 = 0;
    let mut v_a_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: u8 = 0;
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6108_: u8 = 0;
    let mut v___y_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6114_: u8 = 0;
    let mut v___y_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6142_: u8 = 0;
    let mut v___y_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6149_: u8 = 0;
    let mut v___y_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6180_: u8 = 0;
    let mut v___y_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6187_: u8 = 0;
    let mut v___y_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6208_: u8 = 0;
    let mut v___y_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6215_: u8 = 0;
    let mut v___y_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6246_: u8 = 0;
    let mut v___y_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6252_: u8 = 0;
    let mut v___y_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6284_: u8 = 0;
    let mut v___y_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6289_: u8 = 0;
    let mut v___y_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6312_: u8 = 0;
    let mut v___y_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6317_: u8 = 0;
    let mut v___y_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6320_: u8 = 0;
    let mut v_ref_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6337_: u8 = 0;
    let mut v___y_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6339_: u8 = 0;
    let mut v___y_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_argsArray_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: u8 = 0;
    let mut v_ref_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: u8 = 0;
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6371_: u8 = 0;
    let mut v___y_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6380_: u8 = 0;
    let mut v___y_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6387_: usize = 0;
    let mut v___x_6388_: usize = 0;
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6394_: u8 = 0;
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6398_: u8 = 0;
    let mut v_a_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6402_: u8 = 0;
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6406_: u8 = 0;
    let mut v_a_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6410_: u8 = 0;
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6414_: u8 = 0;
    let mut v___y_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6422_: u8 = 0;
    let mut v___y_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6431_: u8 = 0;
    let mut v___y_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suggestions_6435_: u8 = 0;
    let mut v_maxSuggestions_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6444_: u8 = 0;
    let mut v___y_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: u8 = 0;
    let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6469_: u8 = 0;
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6473_: u8 = 0;
    let mut v___y_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6479_: u8 = 0;
    let mut v___y_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6495_: u8 = 0;
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6499_: u8 = 0;
    let mut v___y_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6504_: u8 = 0;
    let mut v___y_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6523_: u8 = 0;
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6527_: u8 = 0;
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6533_: u8 = 0;
    let mut v___y_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_o_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: u8 = 0;
    let mut v___x_6547_: u8 = 0;
    let mut v___x_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: u8 = 0;
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bang_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: u8 = 0;
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cfg_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: u8 = 0;
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: u8 = 0;
    let mut v___x_6582_: u8 = 0;
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_o_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: u8 = 0;
    let mut v___x_6589_: u8 = 0;
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bang_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_5712_ == 0 {
                    lean_dec_ref(v___f_5718_);
                    lean_dec_ref(v___x_5717_);
                    lean_dec_ref(v___x_5716_);
                    lean_dec_ref(v___x_5715_);
                    v___x_5728_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                    return v___x_5728_;
                } else {
                    v___x_5729_ = lean_unsigned_to_nat(0);
                    v_tk_5730_ = l_Lean_Syntax_getArg(v_stx_5713_, v___x_5729_);
                    v___x_6528_ = lean_unsigned_to_nat(1);
                    v___x_6587_ = l_Lean_Syntax_getArg(v_stx_5713_, v___x_6528_);
                    v___x_6588_ = l_Lean_Syntax_isNone(v___x_6587_);
                    if v___x_6588_ == 0 {
                        lean_inc(v___x_6587_);
                        v___x_6589_ = l_Lean_Syntax_matchesNull(v___x_6587_, v___x_6528_);
                        if v___x_6589_ == 0 {
                            lean_dec(v___x_6587_);
                            lean_dec(v_tk_5730_);
                            lean_dec_ref(v___f_5718_);
                            lean_dec_ref(v___x_5717_);
                            lean_dec_ref(v___x_5716_);
                            lean_dec_ref(v___x_5715_);
                            v___x_6590_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                            return v___x_6590_;
                        } else {
                            v_bang_6591_ = l_Lean_Syntax_getArg(v___x_6587_, v___x_5729_);
                            lean_dec(v___x_6587_);
                            v___x_6592_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_6592_, 0, v_bang_6591_);
                            v_bang_6559_ = v___x_6592_;
                            v___y_6560_ = v___y_5719_;
                            v___y_6561_ = v___y_5720_;
                            v___y_6562_ = v___y_5721_;
                            v___y_6563_ = v___y_5722_;
                            v___y_6564_ = v___y_5723_;
                            v___y_6565_ = v___y_5724_;
                            v___y_6566_ = v___y_5725_;
                            v___y_6567_ = v___y_5726_;
                            state = 49;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_6587_);
                        v___x_6593_ = lean_box(0);
                        v_bang_6559_ = v___x_6593_;
                        v___y_6560_ = v___y_5719_;
                        v___y_6561_ = v___y_5720_;
                        v___y_6562_ = v___y_5721_;
                        v___y_6563_ = v___y_5722_;
                        v___y_6564_ = v___y_5723_;
                        v___y_6565_ = v___y_5724_;
                        v___y_6566_ = v___y_5725_;
                        v___y_6567_ = v___y_5726_;
                        state = 49;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5745_ = lean_box((v___x_5714_) as usize);
                v___f_5746_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed as *mut core::ffi::c_void,
                    15,
                    5,
                );
                lean_closure_set(v___f_5746_, 0, v___y_5732_);
                lean_closure_set(v___f_5746_, 1, v___x_5729_);
                lean_closure_set(v___f_5746_, 2, v___x_5745_);
                lean_closure_set(v___f_5746_, 3, v___y_5744_);
                lean_closure_set(v___f_5746_, 4, v___y_5734_);
                v___x_5747_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(
                    v___y_5733_,
                    v___f_5746_,
                    v___y_5740_,
                    v___y_5736_,
                    v___y_5735_,
                    v___y_5743_,
                    v___y_5739_,
                    v___y_5738_,
                    v___y_5742_,
                    v___y_5741_,
                );
                lean_dec(v___y_5733_);
                if lean_obj_tag(v___x_5747_) == 0 {
                    v_a_5748_ = lean_ctor_get(v___x_5747_, 0);
                    lean_inc(v_a_5748_);
                    lean_dec_ref_known(v___x_5747_, 1);
                    v_usedTheorems_5749_ = lean_ctor_get(v_a_5748_, 0);
                    v_diag_5750_ = lean_ctor_get(v_a_5748_, 1);
                    v_isSharedCheck_5792_ = (!lean_is_exclusive(v_a_5748_)) as u8;
                    if v_isSharedCheck_5792_ == 0 {
                        v___x_5752_ = v_a_5748_;
                        v_isShared_5753_ = v_isSharedCheck_5792_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_diag_5750_);
                        lean_inc(v_usedTheorems_5749_);
                        lean_dec(v_a_5748_);
                        v___x_5752_ = lean_box(0);
                        v_isShared_5753_ = v_isSharedCheck_5792_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___y_5737_);
                    lean_dec(v_tk_5730_);
                    v_a_5793_ = lean_ctor_get(v___x_5747_, 0);
                    v_isSharedCheck_5800_ = (!lean_is_exclusive(v___x_5747_)) as u8;
                    if v_isSharedCheck_5800_ == 0 {
                        v___x_5795_ = v___x_5747_;
                        v_isShared_5796_ = v_isSharedCheck_5800_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5793_);
                        lean_dec(v___x_5747_);
                        v___x_5795_ = lean_box(0);
                        v_isShared_5796_ = v_isSharedCheck_5800_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5754_ = l_Lean_Elab_Tactic_mkSimpCallStx(
                    v___y_5737_,
                    v_usedTheorems_5749_,
                    v___y_5739_,
                    v___y_5738_,
                    v___y_5742_,
                    v___y_5741_,
                );
                lean_dec_ref(v_usedTheorems_5749_);
                if lean_obj_tag(v___x_5754_) == 0 {
                    v_a_5755_ = lean_ctor_get(v___x_5754_, 0);
                    lean_inc(v_a_5755_);
                    lean_dec_ref_known(v___x_5754_, 1);
                    v_ref_5756_ = lean_ctor_get(v___y_5742_, 5);
                    v___x_5757_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
                    if v_isShared_5753_ == 0 {
                        lean_ctor_set(v___x_5752_, 1, v_a_5755_);
                        lean_ctor_set(v___x_5752_, 0, v___x_5757_);
                        v___x_5759_ = v___x_5752_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5783_, 0, v___x_5757_);
                        lean_ctor_set(v_reuseFailAlloc_5783_, 1, v_a_5755_);
                        v___x_5759_ = v_reuseFailAlloc_5783_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5752_);
                    lean_dec_ref(v_diag_5750_);
                    lean_dec(v_tk_5730_);
                    v_a_5784_ = lean_ctor_get(v___x_5754_, 0);
                    v_isSharedCheck_5791_ = (!lean_is_exclusive(v___x_5754_)) as u8;
                    if v_isSharedCheck_5791_ == 0 {
                        v___x_5786_ = v___x_5754_;
                        v_isShared_5787_ = v_isSharedCheck_5791_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5784_);
                        lean_dec(v___x_5754_);
                        v___x_5786_ = lean_box(0);
                        v_isShared_5787_ = v_isSharedCheck_5791_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5760_ = lean_box(0);
                v___x_5761_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_5761_, 0, v___x_5759_);
                lean_ctor_set(v___x_5761_, 1, v___x_5760_);
                lean_ctor_set(v___x_5761_, 2, v___x_5760_);
                lean_ctor_set(v___x_5761_, 3, v___x_5760_);
                lean_ctor_set(v___x_5761_, 4, v___x_5760_);
                lean_ctor_set(v___x_5761_, 5, v___x_5760_);
                lean_inc(v_ref_5756_);
                v___x_5762_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5762_, 0, v_ref_5756_);
                v___x_5763_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
                v___x_5764_ = 4;
                v___x_5765_ = l_Lean_MessageData_nil;
                v___x_5766_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_tk_5730_,
                    v___x_5761_,
                    v___x_5762_,
                    v___x_5763_,
                    v___x_5760_,
                    v___x_5764_,
                    v___x_5765_,
                    v___y_5742_,
                    v___y_5741_,
                );
                if lean_obj_tag(v___x_5766_) == 0 {
                    v_isSharedCheck_5773_ = (!lean_is_exclusive(v___x_5766_)) as u8;
                    if v_isSharedCheck_5773_ == 0 {
                        v_unused_5774_ = lean_ctor_get(v___x_5766_, 0);
                        lean_dec(v_unused_5774_);
                        v___x_5768_ = v___x_5766_;
                        v_isShared_5769_ = v_isSharedCheck_5773_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_5766_);
                        v___x_5768_ = lean_box(0);
                        v_isShared_5769_ = v_isSharedCheck_5773_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_diag_5750_);
                    v_a_5775_ = lean_ctor_get(v___x_5766_, 0);
                    v_isSharedCheck_5782_ = (!lean_is_exclusive(v___x_5766_)) as u8;
                    if v_isSharedCheck_5782_ == 0 {
                        v___x_5777_ = v___x_5766_;
                        v_isShared_5778_ = v_isSharedCheck_5782_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5775_);
                        lean_dec(v___x_5766_);
                        v___x_5777_ = lean_box(0);
                        v_isShared_5778_ = v_isSharedCheck_5782_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5769_ == 0 {
                    lean_ctor_set(v___x_5768_, 0, v_diag_5750_);
                    v___x_5771_ = v___x_5768_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5772_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5772_, 0, v_diag_5750_);
                    v___x_5771_ = v_reuseFailAlloc_5772_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5771_;
            }
            6 => {
                if v_isShared_5778_ == 0 {
                    v___x_5780_ = v___x_5777_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5781_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5781_, 0, v_a_5775_);
                    v___x_5780_ = v_reuseFailAlloc_5781_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5780_;
            }
            8 => {
                if v_isShared_5787_ == 0 {
                    v___x_5789_ = v___x_5786_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5790_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
                    v___x_5789_ = v_reuseFailAlloc_5790_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5789_;
            }
            10 => {
                if v_isShared_5796_ == 0 {
                    v___x_5798_ = v___x_5795_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5799_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5799_, 0, v_a_5793_);
                    v___x_5798_ = v_reuseFailAlloc_5799_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5798_;
            }
            12 => {
                v___x_5816_ = 0;
                v___x_5817_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3;
                v___x_5818_ = l_Lean_Elab_Tactic_mkSimpContext(
                    v___y_5803_,
                    v___x_5816_,
                    v___y_5805_,
                    v___x_5816_,
                    v___x_5817_,
                    v___y_5808_,
                    v___y_5809_,
                    v___y_5810_,
                    v___y_5811_,
                    v___y_5812_,
                    v___y_5813_,
                    v___y_5814_,
                    v___y_5815_,
                );
                lean_dec(v___y_5803_);
                if lean_obj_tag(v___x_5818_) == 0 {
                    v_a_5819_ = lean_ctor_get(v___x_5818_, 0);
                    lean_inc(v_a_5819_);
                    lean_dec_ref_known(v___x_5818_, 1);
                    if lean_obj_tag(v___y_5804_) == 0 {
                        v_ctx_5820_ = lean_ctor_get(v_a_5819_, 0);
                        lean_inc_ref(v_ctx_5820_);
                        v_simprocs_5821_ = lean_ctor_get(v_a_5819_, 1);
                        lean_inc_ref(v_simprocs_5821_);
                        v_dischargeWrapper_5822_ = lean_ctor_get(v_a_5819_, 2);
                        lean_inc(v_dischargeWrapper_5822_);
                        lean_dec(v_a_5819_);
                        v___y_5732_ = v___y_5802_;
                        v___y_5733_ = v_dischargeWrapper_5822_;
                        v___y_5734_ = v_simprocs_5821_;
                        v___y_5735_ = v___y_5810_;
                        v___y_5736_ = v___y_5809_;
                        v___y_5737_ = v_stxForSuggestion_5807_;
                        v___y_5738_ = v___y_5813_;
                        v___y_5739_ = v___y_5812_;
                        v___y_5740_ = v___y_5808_;
                        v___y_5741_ = v___y_5815_;
                        v___y_5742_ = v___y_5814_;
                        v___y_5743_ = v___y_5811_;
                        v___y_5744_ = v_ctx_5820_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref_known(v___y_5804_, 1);
                        if v___y_5806_ == 0 {
                            v_ctx_5823_ = lean_ctor_get(v_a_5819_, 0);
                            lean_inc_ref(v_ctx_5823_);
                            v_simprocs_5824_ = lean_ctor_get(v_a_5819_, 1);
                            lean_inc_ref(v_simprocs_5824_);
                            v_dischargeWrapper_5825_ = lean_ctor_get(v_a_5819_, 2);
                            lean_inc(v_dischargeWrapper_5825_);
                            lean_dec(v_a_5819_);
                            v___y_5732_ = v___y_5802_;
                            v___y_5733_ = v_dischargeWrapper_5825_;
                            v___y_5734_ = v_simprocs_5824_;
                            v___y_5735_ = v___y_5810_;
                            v___y_5736_ = v___y_5809_;
                            v___y_5737_ = v_stxForSuggestion_5807_;
                            v___y_5738_ = v___y_5813_;
                            v___y_5739_ = v___y_5812_;
                            v___y_5740_ = v___y_5808_;
                            v___y_5741_ = v___y_5815_;
                            v___y_5742_ = v___y_5814_;
                            v___y_5743_ = v___y_5811_;
                            v___y_5744_ = v_ctx_5823_;
                            state = 1;
                            continue;
                        } else {
                            v_ctx_5826_ = lean_ctor_get(v_a_5819_, 0);
                            lean_inc_ref(v_ctx_5826_);
                            v_simprocs_5827_ = lean_ctor_get(v_a_5819_, 1);
                            lean_inc_ref(v_simprocs_5827_);
                            v_dischargeWrapper_5828_ = lean_ctor_get(v_a_5819_, 2);
                            lean_inc(v_dischargeWrapper_5828_);
                            lean_dec(v_a_5819_);
                            v___x_5829_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_5826_);
                            v___y_5732_ = v___y_5802_;
                            v___y_5733_ = v_dischargeWrapper_5828_;
                            v___y_5734_ = v_simprocs_5827_;
                            v___y_5735_ = v___y_5810_;
                            v___y_5736_ = v___y_5809_;
                            v___y_5737_ = v_stxForSuggestion_5807_;
                            v___y_5738_ = v___y_5813_;
                            v___y_5739_ = v___y_5812_;
                            v___y_5740_ = v___y_5808_;
                            v___y_5741_ = v___y_5815_;
                            v___y_5742_ = v___y_5814_;
                            v___y_5743_ = v___y_5811_;
                            v___y_5744_ = v___x_5829_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_stxForSuggestion_5807_);
                    lean_dec(v___y_5804_);
                    lean_dec(v___y_5802_);
                    lean_dec(v_tk_5730_);
                    v_a_5830_ = lean_ctor_get(v___x_5818_, 0);
                    v_isSharedCheck_5837_ = (!lean_is_exclusive(v___x_5818_)) as u8;
                    if v_isSharedCheck_5837_ == 0 {
                        v___x_5832_ = v___x_5818_;
                        v_isShared_5833_ = v_isSharedCheck_5837_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_5830_);
                        lean_dec(v___x_5818_);
                        v___x_5832_ = lean_box(0);
                        v_isShared_5833_ = v_isSharedCheck_5837_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_5833_ == 0 {
                    v___x_5835_ = v___x_5832_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5836_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_a_5830_);
                    v___x_5835_ = v_reuseFailAlloc_5836_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5835_;
            }
            15 => {
                lean_inc_ref(v___y_5850_);
                v___x_5862_ = l_Array_append___redArg(v___y_5850_, v___y_5861_);
                lean_dec_ref(v___y_5861_);
                lean_inc(v___y_5855_);
                lean_inc(v___y_5859_);
                v___x_5863_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5863_, 0, v___y_5859_);
                lean_ctor_set(v___x_5863_, 1, v___y_5855_);
                lean_ctor_set(v___x_5863_, 2, v___x_5862_);
                v___x_5864_ = l_Lean_Syntax_node6(
                    v___y_5859_,
                    v___y_5852_,
                    v___y_5853_,
                    v___y_5845_,
                    v___y_5856_,
                    v___y_5848_,
                    v___y_5858_,
                    v___x_5863_,
                );
                v___y_5802_ = v___y_5839_;
                v___y_5803_ = v___y_5841_;
                v___y_5804_ = v___y_5843_;
                v___y_5805_ = v___y_5854_;
                v___y_5806_ = v___y_5846_;
                v_stxForSuggestion_5807_ = v___x_5864_;
                v___y_5808_ = v___y_5851_;
                v___y_5809_ = v___y_5842_;
                v___y_5810_ = v___y_5840_;
                v___y_5811_ = v___y_5857_;
                v___y_5812_ = v___y_5860_;
                v___y_5813_ = v___y_5849_;
                v___y_5814_ = v___y_5844_;
                v___y_5815_ = v___y_5847_;
                state = 12;
                continue;
            }
            16 => {
                lean_inc_ref_n(v___y_5878_, 2);
                v___x_5889_ = l_Array_append___redArg(v___y_5878_, v___y_5888_);
                lean_dec_ref(v___y_5888_);
                lean_inc_n(v___y_5885_, 3);
                lean_inc_n(v___y_5886_, 5);
                v___x_5890_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5890_, 0, v___y_5886_);
                lean_ctor_set(v___x_5890_, 1, v___y_5885_);
                lean_ctor_set(v___x_5890_, 2, v___x_5889_);
                v___x_5891_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
                v___x_5892_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5892_, 0, v___y_5886_);
                lean_ctor_set(v___x_5892_, 1, v___x_5891_);
                v___x_5893_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
                v___x_5894_ = l_Lean_Syntax_SepArray_ofElems(v___x_5893_, v___y_5871_);
                lean_dec_ref(v___y_5871_);
                v___x_5895_ = l_Array_append___redArg(v___y_5878_, v___x_5894_);
                lean_dec_ref(v___x_5894_);
                v___x_5896_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5896_, 0, v___y_5886_);
                lean_ctor_set(v___x_5896_, 1, v___y_5885_);
                lean_ctor_set(v___x_5896_, 2, v___x_5895_);
                v___x_5897_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
                v___x_5898_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5898_, 0, v___y_5886_);
                lean_ctor_set(v___x_5898_, 1, v___x_5897_);
                v___x_5899_ = l_Lean_Syntax_node3(
                    v___y_5886_,
                    v___y_5885_,
                    v___x_5892_,
                    v___x_5896_,
                    v___x_5898_,
                );
                if lean_obj_tag(v___y_5876_) == 1 {
                    v_val_5900_ = lean_ctor_get(v___y_5876_, 0);
                    lean_inc(v_val_5900_);
                    lean_dec_ref_known(v___y_5876_, 1);
                    v___x_5901_ = l_Array_mkArray1___redArg(v_val_5900_);
                    v___y_5839_ = v___y_5866_;
                    v___y_5840_ = v___y_5867_;
                    v___y_5841_ = v___y_5868_;
                    v___y_5842_ = v___y_5869_;
                    v___y_5843_ = v___y_5870_;
                    v___y_5844_ = v___y_5872_;
                    v___y_5845_ = v___y_5873_;
                    v___y_5846_ = v___y_5874_;
                    v___y_5847_ = v___y_5875_;
                    v___y_5848_ = v___x_5890_;
                    v___y_5849_ = v___y_5877_;
                    v___y_5850_ = v___y_5878_;
                    v___y_5851_ = v___y_5879_;
                    v___y_5852_ = v___y_5881_;
                    v___y_5853_ = v___y_5880_;
                    v___y_5854_ = v___y_5882_;
                    v___y_5855_ = v___y_5885_;
                    v___y_5856_ = v___y_5884_;
                    v___y_5857_ = v___y_5883_;
                    v___y_5858_ = v___x_5899_;
                    v___y_5859_ = v___y_5886_;
                    v___y_5860_ = v___y_5887_;
                    v___y_5861_ = v___x_5901_;
                    state = 15;
                    continue;
                } else {
                    lean_dec(v___y_5876_);
                    v___x_5902_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_5839_ = v___y_5866_;
                    v___y_5840_ = v___y_5867_;
                    v___y_5841_ = v___y_5868_;
                    v___y_5842_ = v___y_5869_;
                    v___y_5843_ = v___y_5870_;
                    v___y_5844_ = v___y_5872_;
                    v___y_5845_ = v___y_5873_;
                    v___y_5846_ = v___y_5874_;
                    v___y_5847_ = v___y_5875_;
                    v___y_5848_ = v___x_5890_;
                    v___y_5849_ = v___y_5877_;
                    v___y_5850_ = v___y_5878_;
                    v___y_5851_ = v___y_5879_;
                    v___y_5852_ = v___y_5881_;
                    v___y_5853_ = v___y_5880_;
                    v___y_5854_ = v___y_5882_;
                    v___y_5855_ = v___y_5885_;
                    v___y_5856_ = v___y_5884_;
                    v___y_5857_ = v___y_5883_;
                    v___y_5858_ = v___x_5899_;
                    v___y_5859_ = v___y_5886_;
                    v___y_5860_ = v___y_5887_;
                    v___y_5861_ = v___x_5902_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                lean_inc_ref(v___y_5916_);
                v___x_5927_ = l_Array_append___redArg(v___y_5916_, v___y_5926_);
                lean_dec_ref(v___y_5926_);
                lean_inc(v___y_5922_);
                lean_inc(v___y_5924_);
                v___x_5928_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5928_, 0, v___y_5924_);
                lean_ctor_set(v___x_5928_, 1, v___y_5922_);
                lean_ctor_set(v___x_5928_, 2, v___x_5927_);
                if lean_obj_tag(v___y_5923_) == 1 {
                    v_val_5929_ = lean_ctor_get(v___y_5923_, 0);
                    lean_inc(v_val_5929_);
                    lean_dec_ref_known(v___y_5923_, 1);
                    v___x_5930_ = l_Lean_SourceInfo_fromRef(v_val_5929_, v___x_5714_);
                    lean_dec(v_val_5929_);
                    v___x_5931_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_5932_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_5932_, 0, v___x_5930_);
                    lean_ctor_set(v___x_5932_, 1, v___x_5931_);
                    v___x_5933_ = l_Array_mkArray1___redArg(v___x_5932_);
                    v___y_5866_ = v___y_5904_;
                    v___y_5867_ = v___y_5905_;
                    v___y_5868_ = v___y_5906_;
                    v___y_5869_ = v___y_5907_;
                    v___y_5870_ = v___y_5908_;
                    v___y_5871_ = v___y_5909_;
                    v___y_5872_ = v___y_5910_;
                    v___y_5873_ = v___y_5911_;
                    v___y_5874_ = v___y_5912_;
                    v___y_5875_ = v___y_5913_;
                    v___y_5876_ = v___y_5915_;
                    v___y_5877_ = v___y_5914_;
                    v___y_5878_ = v___y_5916_;
                    v___y_5879_ = v___y_5917_;
                    v___y_5880_ = v___y_5919_;
                    v___y_5881_ = v___y_5918_;
                    v___y_5882_ = v___y_5920_;
                    v___y_5883_ = v___y_5921_;
                    v___y_5884_ = v___x_5928_;
                    v___y_5885_ = v___y_5922_;
                    v___y_5886_ = v___y_5924_;
                    v___y_5887_ = v___y_5925_;
                    v___y_5888_ = v___x_5933_;
                    state = 16;
                    continue;
                } else {
                    lean_dec(v___y_5923_);
                    v___x_5934_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_5866_ = v___y_5904_;
                    v___y_5867_ = v___y_5905_;
                    v___y_5868_ = v___y_5906_;
                    v___y_5869_ = v___y_5907_;
                    v___y_5870_ = v___y_5908_;
                    v___y_5871_ = v___y_5909_;
                    v___y_5872_ = v___y_5910_;
                    v___y_5873_ = v___y_5911_;
                    v___y_5874_ = v___y_5912_;
                    v___y_5875_ = v___y_5913_;
                    v___y_5876_ = v___y_5915_;
                    v___y_5877_ = v___y_5914_;
                    v___y_5878_ = v___y_5916_;
                    v___y_5879_ = v___y_5917_;
                    v___y_5880_ = v___y_5919_;
                    v___y_5881_ = v___y_5918_;
                    v___y_5882_ = v___y_5920_;
                    v___y_5883_ = v___y_5921_;
                    v___y_5884_ = v___x_5928_;
                    v___y_5885_ = v___y_5922_;
                    v___y_5886_ = v___y_5924_;
                    v___y_5887_ = v___y_5925_;
                    v___y_5888_ = v___x_5934_;
                    state = 16;
                    continue;
                }
            }
            18 => {
                lean_inc_ref(v___y_5937_);
                v___x_5959_ = l_Array_append___redArg(v___y_5937_, v___y_5958_);
                lean_dec_ref(v___y_5958_);
                lean_inc(v___y_5941_);
                lean_inc(v___y_5955_);
                v___x_5960_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5960_, 0, v___y_5955_);
                lean_ctor_set(v___x_5960_, 1, v___y_5941_);
                lean_ctor_set(v___x_5960_, 2, v___x_5959_);
                v___x_5961_ = l_Lean_Syntax_node6(
                    v___y_5955_,
                    v___y_5948_,
                    v___y_5942_,
                    v___y_5946_,
                    v___y_5952_,
                    v___y_5956_,
                    v___y_5940_,
                    v___x_5960_,
                );
                v___y_5802_ = v___y_5936_;
                v___y_5803_ = v___y_5939_;
                v___y_5804_ = v___y_5944_;
                v___y_5805_ = v___y_5953_;
                v___y_5806_ = v___y_5947_;
                v_stxForSuggestion_5807_ = v___x_5961_;
                v___y_5808_ = v___y_5951_;
                v___y_5809_ = v___y_5943_;
                v___y_5810_ = v___y_5938_;
                v___y_5811_ = v___y_5954_;
                v___y_5812_ = v___y_5957_;
                v___y_5813_ = v___y_5950_;
                v___y_5814_ = v___y_5945_;
                v___y_5815_ = v___y_5949_;
                state = 12;
                continue;
            }
            19 => {
                lean_inc_ref_n(v___y_5964_, 2);
                v___x_5986_ = l_Array_append___redArg(v___y_5964_, v___y_5985_);
                lean_dec_ref(v___y_5985_);
                lean_inc_n(v___y_5967_, 3);
                lean_inc_n(v___y_5983_, 5);
                v___x_5987_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5987_, 0, v___y_5983_);
                lean_ctor_set(v___x_5987_, 1, v___y_5967_);
                lean_ctor_set(v___x_5987_, 2, v___x_5986_);
                v___x_5988_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
                v___x_5989_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5989_, 0, v___y_5983_);
                lean_ctor_set(v___x_5989_, 1, v___x_5988_);
                v___x_5990_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
                v___x_5991_ = l_Lean_Syntax_SepArray_ofElems(v___x_5990_, v___y_5971_);
                lean_dec_ref(v___y_5971_);
                v___x_5992_ = l_Array_append___redArg(v___y_5964_, v___x_5991_);
                lean_dec_ref(v___x_5991_);
                v___x_5993_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5993_, 0, v___y_5983_);
                lean_ctor_set(v___x_5993_, 1, v___y_5967_);
                lean_ctor_set(v___x_5993_, 2, v___x_5992_);
                v___x_5994_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
                v___x_5995_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5995_, 0, v___y_5983_);
                lean_ctor_set(v___x_5995_, 1, v___x_5994_);
                v___x_5996_ = l_Lean_Syntax_node3(
                    v___y_5983_,
                    v___y_5967_,
                    v___x_5989_,
                    v___x_5993_,
                    v___x_5995_,
                );
                if lean_obj_tag(v___y_5977_) == 1 {
                    v_val_5997_ = lean_ctor_get(v___y_5977_, 0);
                    lean_inc(v_val_5997_);
                    lean_dec_ref_known(v___y_5977_, 1);
                    v___x_5998_ = l_Array_mkArray1___redArg(v_val_5997_);
                    v___y_5936_ = v___y_5963_;
                    v___y_5937_ = v___y_5964_;
                    v___y_5938_ = v___y_5965_;
                    v___y_5939_ = v___y_5966_;
                    v___y_5940_ = v___x_5996_;
                    v___y_5941_ = v___y_5967_;
                    v___y_5942_ = v___y_5968_;
                    v___y_5943_ = v___y_5969_;
                    v___y_5944_ = v___y_5970_;
                    v___y_5945_ = v___y_5972_;
                    v___y_5946_ = v___y_5973_;
                    v___y_5947_ = v___y_5974_;
                    v___y_5948_ = v___y_5975_;
                    v___y_5949_ = v___y_5976_;
                    v___y_5950_ = v___y_5978_;
                    v___y_5951_ = v___y_5979_;
                    v___y_5952_ = v___y_5980_;
                    v___y_5953_ = v___y_5981_;
                    v___y_5954_ = v___y_5982_;
                    v___y_5955_ = v___y_5983_;
                    v___y_5956_ = v___x_5987_;
                    v___y_5957_ = v___y_5984_;
                    v___y_5958_ = v___x_5998_;
                    state = 18;
                    continue;
                } else {
                    lean_dec(v___y_5977_);
                    v___x_5999_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_5936_ = v___y_5963_;
                    v___y_5937_ = v___y_5964_;
                    v___y_5938_ = v___y_5965_;
                    v___y_5939_ = v___y_5966_;
                    v___y_5940_ = v___x_5996_;
                    v___y_5941_ = v___y_5967_;
                    v___y_5942_ = v___y_5968_;
                    v___y_5943_ = v___y_5969_;
                    v___y_5944_ = v___y_5970_;
                    v___y_5945_ = v___y_5972_;
                    v___y_5946_ = v___y_5973_;
                    v___y_5947_ = v___y_5974_;
                    v___y_5948_ = v___y_5975_;
                    v___y_5949_ = v___y_5976_;
                    v___y_5950_ = v___y_5978_;
                    v___y_5951_ = v___y_5979_;
                    v___y_5952_ = v___y_5980_;
                    v___y_5953_ = v___y_5981_;
                    v___y_5954_ = v___y_5982_;
                    v___y_5955_ = v___y_5983_;
                    v___y_5956_ = v___x_5987_;
                    v___y_5957_ = v___y_5984_;
                    v___y_5958_ = v___x_5999_;
                    state = 18;
                    continue;
                }
            }
            20 => {
                lean_inc_ref(v___y_6002_);
                v___x_6024_ = l_Array_append___redArg(v___y_6002_, v___y_6023_);
                lean_dec_ref(v___y_6023_);
                lean_inc(v___y_6005_);
                lean_inc(v___y_6020_);
                v___x_6025_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6025_, 0, v___y_6020_);
                lean_ctor_set(v___x_6025_, 1, v___y_6005_);
                lean_ctor_set(v___x_6025_, 2, v___x_6024_);
                if lean_obj_tag(v___y_6021_) == 1 {
                    v_val_6026_ = lean_ctor_get(v___y_6021_, 0);
                    lean_inc(v_val_6026_);
                    lean_dec_ref_known(v___y_6021_, 1);
                    v___x_6027_ = l_Lean_SourceInfo_fromRef(v_val_6026_, v___x_5714_);
                    lean_dec(v_val_6026_);
                    v___x_6028_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_6029_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_6029_, 0, v___x_6027_);
                    lean_ctor_set(v___x_6029_, 1, v___x_6028_);
                    v___x_6030_ = l_Array_mkArray1___redArg(v___x_6029_);
                    v___y_5963_ = v___y_6001_;
                    v___y_5964_ = v___y_6002_;
                    v___y_5965_ = v___y_6003_;
                    v___y_5966_ = v___y_6004_;
                    v___y_5967_ = v___y_6005_;
                    v___y_5968_ = v___y_6006_;
                    v___y_5969_ = v___y_6007_;
                    v___y_5970_ = v___y_6008_;
                    v___y_5971_ = v___y_6009_;
                    v___y_5972_ = v___y_6010_;
                    v___y_5973_ = v___y_6011_;
                    v___y_5974_ = v___y_6012_;
                    v___y_5975_ = v___y_6013_;
                    v___y_5976_ = v___y_6014_;
                    v___y_5977_ = v___y_6016_;
                    v___y_5978_ = v___y_6015_;
                    v___y_5979_ = v___y_6017_;
                    v___y_5980_ = v___x_6025_;
                    v___y_5981_ = v___y_6018_;
                    v___y_5982_ = v___y_6019_;
                    v___y_5983_ = v___y_6020_;
                    v___y_5984_ = v___y_6022_;
                    v___y_5985_ = v___x_6030_;
                    state = 19;
                    continue;
                } else {
                    lean_dec(v___y_6021_);
                    v___x_6031_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_5963_ = v___y_6001_;
                    v___y_5964_ = v___y_6002_;
                    v___y_5965_ = v___y_6003_;
                    v___y_5966_ = v___y_6004_;
                    v___y_5967_ = v___y_6005_;
                    v___y_5968_ = v___y_6006_;
                    v___y_5969_ = v___y_6007_;
                    v___y_5970_ = v___y_6008_;
                    v___y_5971_ = v___y_6009_;
                    v___y_5972_ = v___y_6010_;
                    v___y_5973_ = v___y_6011_;
                    v___y_5974_ = v___y_6012_;
                    v___y_5975_ = v___y_6013_;
                    v___y_5976_ = v___y_6014_;
                    v___y_5977_ = v___y_6016_;
                    v___y_5978_ = v___y_6015_;
                    v___y_5979_ = v___y_6017_;
                    v___y_5980_ = v___x_6025_;
                    v___y_5981_ = v___y_6018_;
                    v___y_5982_ = v___y_6019_;
                    v___y_5983_ = v___y_6020_;
                    v___y_5984_ = v___y_6022_;
                    v___y_5985_ = v___x_6031_;
                    state = 19;
                    continue;
                }
            }
            21 => {
                v_ref_6052_ = lean_ctor_get(v___y_6039_, 5);
                v___x_6053_ = l_Lean_SourceInfo_fromRef(v_ref_6052_, v___y_6051_);
                v___x_6054_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
                v___x_6055_ =
                    l_Lean_Name_mkStr4(v___x_5715_, v___x_5716_, v___x_5717_, v___x_6054_);
                v___x_6056_ = l_Lean_SourceInfo_fromRef(v_tk_5730_, v___x_5714_);
                v___x_6057_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6057_, 0, v___x_6056_);
                lean_ctor_set(v___x_6057_, 1, v___x_6054_);
                v___x_6058_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                v___x_6059_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                if lean_obj_tag(v___y_6035_) == 1 {
                    v_val_6060_ = lean_ctor_get(v___y_6035_, 0);
                    lean_inc(v_val_6060_);
                    lean_dec_ref_known(v___y_6035_, 1);
                    v___x_6061_ = l_Array_mkArray1___redArg(v_val_6060_);
                    v___y_6001_ = v___y_6033_;
                    v___y_6002_ = v___x_6059_;
                    v___y_6003_ = v___y_6034_;
                    v___y_6004_ = v___y_6036_;
                    v___y_6005_ = v___x_6058_;
                    v___y_6006_ = v___x_6057_;
                    v___y_6007_ = v___y_6037_;
                    v___y_6008_ = v___y_6038_;
                    v___y_6009_ = v___y_6040_;
                    v___y_6010_ = v___y_6039_;
                    v___y_6011_ = v___y_6041_;
                    v___y_6012_ = v___y_6042_;
                    v___y_6013_ = v___x_6055_;
                    v___y_6014_ = v___y_6043_;
                    v___y_6015_ = v___y_6044_;
                    v___y_6016_ = v___y_6045_;
                    v___y_6017_ = v___y_6046_;
                    v___y_6018_ = v___y_6047_;
                    v___y_6019_ = v___y_6048_;
                    v___y_6020_ = v___x_6053_;
                    v___y_6021_ = v___y_6049_;
                    v___y_6022_ = v___y_6050_;
                    v___y_6023_ = v___x_6061_;
                    state = 20;
                    continue;
                } else {
                    lean_dec(v___y_6035_);
                    v___x_6062_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_6001_ = v___y_6033_;
                    v___y_6002_ = v___x_6059_;
                    v___y_6003_ = v___y_6034_;
                    v___y_6004_ = v___y_6036_;
                    v___y_6005_ = v___x_6058_;
                    v___y_6006_ = v___x_6057_;
                    v___y_6007_ = v___y_6037_;
                    v___y_6008_ = v___y_6038_;
                    v___y_6009_ = v___y_6040_;
                    v___y_6010_ = v___y_6039_;
                    v___y_6011_ = v___y_6041_;
                    v___y_6012_ = v___y_6042_;
                    v___y_6013_ = v___x_6055_;
                    v___y_6014_ = v___y_6043_;
                    v___y_6015_ = v___y_6044_;
                    v___y_6016_ = v___y_6045_;
                    v___y_6017_ = v___y_6046_;
                    v___y_6018_ = v___y_6047_;
                    v___y_6019_ = v___y_6048_;
                    v___y_6020_ = v___x_6053_;
                    v___y_6021_ = v___y_6049_;
                    v___y_6022_ = v___y_6050_;
                    v___y_6023_ = v___x_6062_;
                    state = 20;
                    continue;
                }
            }
            22 => {
                v___x_6082_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(
                    v___y_6067_,
                );
                if lean_obj_tag(v___y_6069_) == 0 {
                    v_a_6083_ = lean_ctor_get(v___x_6082_, 0);
                    lean_inc(v_a_6083_);
                    lean_dec_ref(v___x_6082_);
                    v___x_6084_ = 0;
                    v___y_6033_ = v___y_6064_;
                    v___y_6034_ = v___y_6076_;
                    v___y_6035_ = v___y_6066_;
                    v___y_6036_ = v_stxForExecution_6073_;
                    v___y_6037_ = v___y_6075_;
                    v___y_6038_ = v___y_6069_;
                    v___y_6039_ = v___y_6080_;
                    v___y_6040_ = v___y_6070_;
                    v___y_6041_ = v_a_6083_;
                    v___y_6042_ = v___y_6071_;
                    v___y_6043_ = v___y_6081_;
                    v___y_6044_ = v___y_6079_;
                    v___y_6045_ = v___y_6065_;
                    v___y_6046_ = v___y_6074_;
                    v___y_6047_ = v___y_6068_;
                    v___y_6048_ = v___y_6077_;
                    v___y_6049_ = v___y_6072_;
                    v___y_6050_ = v___y_6078_;
                    v___y_6051_ = v___x_6084_;
                    state = 21;
                    continue;
                } else {
                    if v___y_6071_ == 0 {
                        v_a_6085_ = lean_ctor_get(v___x_6082_, 0);
                        lean_inc(v_a_6085_);
                        lean_dec_ref(v___x_6082_);
                        v___y_6033_ = v___y_6064_;
                        v___y_6034_ = v___y_6076_;
                        v___y_6035_ = v___y_6066_;
                        v___y_6036_ = v_stxForExecution_6073_;
                        v___y_6037_ = v___y_6075_;
                        v___y_6038_ = v___y_6069_;
                        v___y_6039_ = v___y_6080_;
                        v___y_6040_ = v___y_6070_;
                        v___y_6041_ = v_a_6085_;
                        v___y_6042_ = v___y_6071_;
                        v___y_6043_ = v___y_6081_;
                        v___y_6044_ = v___y_6079_;
                        v___y_6045_ = v___y_6065_;
                        v___y_6046_ = v___y_6074_;
                        v___y_6047_ = v___y_6068_;
                        v___y_6048_ = v___y_6077_;
                        v___y_6049_ = v___y_6072_;
                        v___y_6050_ = v___y_6078_;
                        v___y_6051_ = v___y_6071_;
                        state = 21;
                        continue;
                    } else {
                        v_a_6086_ = lean_ctor_get(v___x_6082_, 0);
                        lean_inc(v_a_6086_);
                        lean_dec_ref(v___x_6082_);
                        v_ref_6087_ = lean_ctor_get(v___y_6080_, 5);
                        v___x_6088_ = 0;
                        v___x_6089_ = l_Lean_SourceInfo_fromRef(v_ref_6087_, v___x_6088_);
                        v___x_6090_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
                        v___x_6091_ =
                            l_Lean_Name_mkStr4(v___x_5715_, v___x_5716_, v___x_5717_, v___x_6090_);
                        v___x_6092_ = l_Lean_SourceInfo_fromRef(v_tk_5730_, v___x_5714_);
                        v___x_6093_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11;
                        v___x_6094_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_6094_, 0, v___x_6092_);
                        lean_ctor_set(v___x_6094_, 1, v___x_6093_);
                        v___x_6095_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                        v___x_6096_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                        if lean_obj_tag(v___y_6066_) == 1 {
                            v_val_6097_ = lean_ctor_get(v___y_6066_, 0);
                            lean_inc(v_val_6097_);
                            lean_dec_ref_known(v___y_6066_, 1);
                            v___x_6098_ = l_Array_mkArray1___redArg(v_val_6097_);
                            v___y_5904_ = v___y_6064_;
                            v___y_5905_ = v___y_6076_;
                            v___y_5906_ = v_stxForExecution_6073_;
                            v___y_5907_ = v___y_6075_;
                            v___y_5908_ = v___y_6069_;
                            v___y_5909_ = v___y_6070_;
                            v___y_5910_ = v___y_6080_;
                            v___y_5911_ = v_a_6086_;
                            v___y_5912_ = v___y_6071_;
                            v___y_5913_ = v___y_6081_;
                            v___y_5914_ = v___y_6079_;
                            v___y_5915_ = v___y_6065_;
                            v___y_5916_ = v___x_6096_;
                            v___y_5917_ = v___y_6074_;
                            v___y_5918_ = v___x_6091_;
                            v___y_5919_ = v___x_6094_;
                            v___y_5920_ = v___y_6068_;
                            v___y_5921_ = v___y_6077_;
                            v___y_5922_ = v___x_6095_;
                            v___y_5923_ = v___y_6072_;
                            v___y_5924_ = v___x_6089_;
                            v___y_5925_ = v___y_6078_;
                            v___y_5926_ = v___x_6098_;
                            state = 17;
                            continue;
                        } else {
                            lean_dec(v___y_6066_);
                            v___x_6099_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                            v___y_5904_ = v___y_6064_;
                            v___y_5905_ = v___y_6076_;
                            v___y_5906_ = v_stxForExecution_6073_;
                            v___y_5907_ = v___y_6075_;
                            v___y_5908_ = v___y_6069_;
                            v___y_5909_ = v___y_6070_;
                            v___y_5910_ = v___y_6080_;
                            v___y_5911_ = v_a_6086_;
                            v___y_5912_ = v___y_6071_;
                            v___y_5913_ = v___y_6081_;
                            v___y_5914_ = v___y_6079_;
                            v___y_5915_ = v___y_6065_;
                            v___y_5916_ = v___x_6096_;
                            v___y_5917_ = v___y_6074_;
                            v___y_5918_ = v___x_6091_;
                            v___y_5919_ = v___x_6094_;
                            v___y_5920_ = v___y_6068_;
                            v___y_5921_ = v___y_6077_;
                            v___y_5922_ = v___x_6095_;
                            v___y_5923_ = v___y_6072_;
                            v___y_5924_ = v___x_6089_;
                            v___y_5925_ = v___y_6078_;
                            v___y_5926_ = v___x_6099_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            23 => {
                lean_inc_ref(v___y_6124_);
                v___x_6127_ = l_Array_append___redArg(v___y_6124_, v___y_6126_);
                lean_dec_ref(v___y_6126_);
                lean_inc(v___y_6112_);
                lean_inc(v___y_6122_);
                v___x_6128_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6128_, 0, v___y_6122_);
                lean_ctor_set(v___x_6128_, 1, v___y_6112_);
                lean_ctor_set(v___x_6128_, 2, v___x_6127_);
                lean_inc(v___y_6118_);
                v___x_6129_ = l_Lean_Syntax_node6(
                    v___y_6122_,
                    v___y_6116_,
                    v___y_6106_,
                    v___y_6118_,
                    v___y_6104_,
                    v___y_6123_,
                    v___y_6102_,
                    v___x_6128_,
                );
                v___y_6064_ = v___y_6101_;
                v___y_6065_ = v___y_6111_;
                v___y_6066_ = v___y_6103_;
                v___y_6067_ = v___y_6118_;
                v___y_6068_ = v___y_6114_;
                v___y_6069_ = v___y_6119_;
                v___y_6070_ = v___y_6107_;
                v___y_6071_ = v___y_6108_;
                v___y_6072_ = v___y_6125_;
                v_stxForExecution_6073_ = v___x_6129_;
                v___y_6074_ = v___y_6105_;
                v___y_6075_ = v___y_6117_;
                v___y_6076_ = v___y_6121_;
                v___y_6077_ = v___y_6110_;
                v___y_6078_ = v___y_6115_;
                v___y_6079_ = v___y_6120_;
                v___y_6080_ = v___y_6113_;
                v___y_6081_ = v___y_6109_;
                state = 22;
                continue;
            }
            24 => {
                lean_inc_ref_n(v___y_6150_, 2);
                v___x_6155_ = l_Array_append___redArg(v___y_6150_, v___y_6154_);
                lean_dec_ref(v___y_6154_);
                lean_inc_n(v___y_6147_, 3);
                lean_inc_n(v___y_6143_, 5);
                v___x_6156_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6156_, 0, v___y_6143_);
                lean_ctor_set(v___x_6156_, 1, v___y_6147_);
                lean_ctor_set(v___x_6156_, 2, v___x_6155_);
                v___x_6157_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
                v___x_6158_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6158_, 0, v___y_6143_);
                lean_ctor_set(v___x_6158_, 1, v___x_6157_);
                v___x_6159_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
                v___x_6160_ = l_Lean_Syntax_SepArray_ofElems(v___x_6159_, v___y_6141_);
                v___x_6161_ = l_Array_append___redArg(v___y_6150_, v___x_6160_);
                lean_dec_ref(v___x_6160_);
                v___x_6162_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6162_, 0, v___y_6143_);
                lean_ctor_set(v___x_6162_, 1, v___y_6147_);
                lean_ctor_set(v___x_6162_, 2, v___x_6161_);
                v___x_6163_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
                v___x_6164_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6164_, 0, v___y_6143_);
                lean_ctor_set(v___x_6164_, 1, v___x_6163_);
                v___x_6165_ = l_Lean_Syntax_node3(
                    v___y_6143_,
                    v___y_6147_,
                    v___x_6158_,
                    v___x_6162_,
                    v___x_6164_,
                );
                if lean_obj_tag(v___y_6146_) == 1 {
                    v_val_6166_ = lean_ctor_get(v___y_6146_, 0);
                    lean_inc(v_val_6166_);
                    v___x_6167_ = l_Array_mkArray1___redArg(v_val_6166_);
                    v___y_6101_ = v___y_6131_;
                    v___y_6102_ = v___x_6165_;
                    v___y_6103_ = v___y_6133_;
                    v___y_6104_ = v___y_6134_;
                    v___y_6105_ = v___y_6138_;
                    v___y_6106_ = v___y_6139_;
                    v___y_6107_ = v___y_6141_;
                    v___y_6108_ = v___y_6142_;
                    v___y_6109_ = v___y_6144_;
                    v___y_6110_ = v___y_6145_;
                    v___y_6111_ = v___y_6146_;
                    v___y_6112_ = v___y_6147_;
                    v___y_6113_ = v___y_6148_;
                    v___y_6114_ = v___y_6149_;
                    v___y_6115_ = v___y_6152_;
                    v___y_6116_ = v___y_6153_;
                    v___y_6117_ = v___y_6132_;
                    v___y_6118_ = v___y_6136_;
                    v___y_6119_ = v___y_6135_;
                    v___y_6120_ = v___y_6137_;
                    v___y_6121_ = v___y_6140_;
                    v___y_6122_ = v___y_6143_;
                    v___y_6123_ = v___x_6156_;
                    v___y_6124_ = v___y_6150_;
                    v___y_6125_ = v___y_6151_;
                    v___y_6126_ = v___x_6167_;
                    state = 23;
                    continue;
                } else {
                    v___x_6168_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_6101_ = v___y_6131_;
                    v___y_6102_ = v___x_6165_;
                    v___y_6103_ = v___y_6133_;
                    v___y_6104_ = v___y_6134_;
                    v___y_6105_ = v___y_6138_;
                    v___y_6106_ = v___y_6139_;
                    v___y_6107_ = v___y_6141_;
                    v___y_6108_ = v___y_6142_;
                    v___y_6109_ = v___y_6144_;
                    v___y_6110_ = v___y_6145_;
                    v___y_6111_ = v___y_6146_;
                    v___y_6112_ = v___y_6147_;
                    v___y_6113_ = v___y_6148_;
                    v___y_6114_ = v___y_6149_;
                    v___y_6115_ = v___y_6152_;
                    v___y_6116_ = v___y_6153_;
                    v___y_6117_ = v___y_6132_;
                    v___y_6118_ = v___y_6136_;
                    v___y_6119_ = v___y_6135_;
                    v___y_6120_ = v___y_6137_;
                    v___y_6121_ = v___y_6140_;
                    v___y_6122_ = v___y_6143_;
                    v___y_6123_ = v___x_6156_;
                    v___y_6124_ = v___y_6150_;
                    v___y_6125_ = v___y_6151_;
                    v___y_6126_ = v___x_6168_;
                    state = 23;
                    continue;
                }
            }
            25 => {
                lean_inc_ref(v___y_6188_);
                v___x_6193_ = l_Array_append___redArg(v___y_6188_, v___y_6192_);
                lean_dec_ref(v___y_6192_);
                lean_inc(v___y_6186_);
                lean_inc(v___y_6181_);
                v___x_6194_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6194_, 0, v___y_6181_);
                lean_ctor_set(v___x_6194_, 1, v___y_6186_);
                lean_ctor_set(v___x_6194_, 2, v___x_6193_);
                if lean_obj_tag(v___y_6190_) == 1 {
                    v_val_6195_ = lean_ctor_get(v___y_6190_, 0);
                    v___x_6196_ = l_Lean_SourceInfo_fromRef(v_val_6195_, v___x_5714_);
                    v___x_6197_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_6198_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_6198_, 0, v___x_6196_);
                    lean_ctor_set(v___x_6198_, 1, v___x_6197_);
                    v___x_6199_ = l_Array_mkArray1___redArg(v___x_6198_);
                    v___y_6131_ = v___y_6170_;
                    v___y_6132_ = v___y_6171_;
                    v___y_6133_ = v___y_6172_;
                    v___y_6134_ = v___x_6194_;
                    v___y_6135_ = v___y_6173_;
                    v___y_6136_ = v___y_6174_;
                    v___y_6137_ = v___y_6175_;
                    v___y_6138_ = v___y_6176_;
                    v___y_6139_ = v___y_6177_;
                    v___y_6140_ = v___y_6178_;
                    v___y_6141_ = v___y_6179_;
                    v___y_6142_ = v___y_6180_;
                    v___y_6143_ = v___y_6181_;
                    v___y_6144_ = v___y_6182_;
                    v___y_6145_ = v___y_6183_;
                    v___y_6146_ = v___y_6184_;
                    v___y_6147_ = v___y_6186_;
                    v___y_6148_ = v___y_6185_;
                    v___y_6149_ = v___y_6187_;
                    v___y_6150_ = v___y_6188_;
                    v___y_6151_ = v___y_6190_;
                    v___y_6152_ = v___y_6189_;
                    v___y_6153_ = v___y_6191_;
                    v___y_6154_ = v___x_6199_;
                    state = 24;
                    continue;
                } else {
                    v___x_6200_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_6131_ = v___y_6170_;
                    v___y_6132_ = v___y_6171_;
                    v___y_6133_ = v___y_6172_;
                    v___y_6134_ = v___x_6194_;
                    v___y_6135_ = v___y_6173_;
                    v___y_6136_ = v___y_6174_;
                    v___y_6137_ = v___y_6175_;
                    v___y_6138_ = v___y_6176_;
                    v___y_6139_ = v___y_6177_;
                    v___y_6140_ = v___y_6178_;
                    v___y_6141_ = v___y_6179_;
                    v___y_6142_ = v___y_6180_;
                    v___y_6143_ = v___y_6181_;
                    v___y_6144_ = v___y_6182_;
                    v___y_6145_ = v___y_6183_;
                    v___y_6146_ = v___y_6184_;
                    v___y_6147_ = v___y_6186_;
                    v___y_6148_ = v___y_6185_;
                    v___y_6149_ = v___y_6187_;
                    v___y_6150_ = v___y_6188_;
                    v___y_6151_ = v___y_6190_;
                    v___y_6152_ = v___y_6189_;
                    v___y_6153_ = v___y_6191_;
                    v___y_6154_ = v___x_6200_;
                    state = 24;
                    continue;
                }
            }
            26 => {
                lean_inc_ref(v___y_6225_);
                v___x_6228_ = l_Array_append___redArg(v___y_6225_, v___y_6227_);
                lean_dec_ref(v___y_6227_);
                lean_inc(v___y_6203_);
                lean_inc(v___y_6206_);
                v___x_6229_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6229_, 0, v___y_6206_);
                lean_ctor_set(v___x_6229_, 1, v___y_6203_);
                lean_ctor_set(v___x_6229_, 2, v___x_6228_);
                lean_inc(v___y_6220_);
                v___x_6230_ = l_Lean_Syntax_node6(
                    v___y_6206_,
                    v___y_6218_,
                    v___y_6223_,
                    v___y_6220_,
                    v___y_6219_,
                    v___y_6211_,
                    v___y_6213_,
                    v___x_6229_,
                );
                v___y_6064_ = v___y_6202_;
                v___y_6065_ = v___y_6212_;
                v___y_6066_ = v___y_6204_;
                v___y_6067_ = v___y_6220_;
                v___y_6068_ = v___y_6215_;
                v___y_6069_ = v___y_6221_;
                v___y_6070_ = v___y_6207_;
                v___y_6071_ = v___y_6208_;
                v___y_6072_ = v___y_6226_;
                v_stxForExecution_6073_ = v___x_6230_;
                v___y_6074_ = v___y_6205_;
                v___y_6075_ = v___y_6217_;
                v___y_6076_ = v___y_6224_;
                v___y_6077_ = v___y_6210_;
                v___y_6078_ = v___y_6216_;
                v___y_6079_ = v___y_6222_;
                v___y_6080_ = v___y_6214_;
                v___y_6081_ = v___y_6209_;
                state = 22;
                continue;
            }
            27 => {
                lean_inc_ref_n(v___y_6251_, 2);
                v___x_6256_ = l_Array_append___redArg(v___y_6251_, v___y_6255_);
                lean_dec_ref(v___y_6255_);
                lean_inc_n(v___y_6235_, 3);
                lean_inc_n(v___y_6241_, 5);
                v___x_6257_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6257_, 0, v___y_6241_);
                lean_ctor_set(v___x_6257_, 1, v___y_6235_);
                lean_ctor_set(v___x_6257_, 2, v___x_6256_);
                v___x_6258_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
                v___x_6259_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6259_, 0, v___y_6241_);
                lean_ctor_set(v___x_6259_, 1, v___x_6258_);
                v___x_6260_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
                v___x_6261_ = l_Lean_Syntax_SepArray_ofElems(v___x_6260_, v___y_6245_);
                v___x_6262_ = l_Array_append___redArg(v___y_6251_, v___x_6261_);
                lean_dec_ref(v___x_6261_);
                v___x_6263_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6263_, 0, v___y_6241_);
                lean_ctor_set(v___x_6263_, 1, v___y_6235_);
                lean_ctor_set(v___x_6263_, 2, v___x_6262_);
                v___x_6264_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
                v___x_6265_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6265_, 0, v___y_6241_);
                lean_ctor_set(v___x_6265_, 1, v___x_6264_);
                v___x_6266_ = l_Lean_Syntax_node3(
                    v___y_6241_,
                    v___y_6235_,
                    v___x_6259_,
                    v___x_6263_,
                    v___x_6265_,
                );
                if lean_obj_tag(v___y_6249_) == 1 {
                    v_val_6267_ = lean_ctor_get(v___y_6249_, 0);
                    lean_inc(v_val_6267_);
                    v___x_6268_ = l_Array_mkArray1___redArg(v_val_6267_);
                    v___y_6202_ = v___y_6232_;
                    v___y_6203_ = v___y_6235_;
                    v___y_6204_ = v___y_6236_;
                    v___y_6205_ = v___y_6242_;
                    v___y_6206_ = v___y_6241_;
                    v___y_6207_ = v___y_6245_;
                    v___y_6208_ = v___y_6246_;
                    v___y_6209_ = v___y_6247_;
                    v___y_6210_ = v___y_6248_;
                    v___y_6211_ = v___x_6257_;
                    v___y_6212_ = v___y_6249_;
                    v___y_6213_ = v___x_6266_;
                    v___y_6214_ = v___y_6250_;
                    v___y_6215_ = v___y_6252_;
                    v___y_6216_ = v___y_6254_;
                    v___y_6217_ = v___y_6234_;
                    v___y_6218_ = v___y_6233_;
                    v___y_6219_ = v___y_6239_;
                    v___y_6220_ = v___y_6238_;
                    v___y_6221_ = v___y_6237_;
                    v___y_6222_ = v___y_6240_;
                    v___y_6223_ = v___y_6243_;
                    v___y_6224_ = v___y_6244_;
                    v___y_6225_ = v___y_6251_;
                    v___y_6226_ = v___y_6253_;
                    v___y_6227_ = v___x_6268_;
                    state = 26;
                    continue;
                } else {
                    v___x_6269_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_6202_ = v___y_6232_;
                    v___y_6203_ = v___y_6235_;
                    v___y_6204_ = v___y_6236_;
                    v___y_6205_ = v___y_6242_;
                    v___y_6206_ = v___y_6241_;
                    v___y_6207_ = v___y_6245_;
                    v___y_6208_ = v___y_6246_;
                    v___y_6209_ = v___y_6247_;
                    v___y_6210_ = v___y_6248_;
                    v___y_6211_ = v___x_6257_;
                    v___y_6212_ = v___y_6249_;
                    v___y_6213_ = v___x_6266_;
                    v___y_6214_ = v___y_6250_;
                    v___y_6215_ = v___y_6252_;
                    v___y_6216_ = v___y_6254_;
                    v___y_6217_ = v___y_6234_;
                    v___y_6218_ = v___y_6233_;
                    v___y_6219_ = v___y_6239_;
                    v___y_6220_ = v___y_6238_;
                    v___y_6221_ = v___y_6237_;
                    v___y_6222_ = v___y_6240_;
                    v___y_6223_ = v___y_6243_;
                    v___y_6224_ = v___y_6244_;
                    v___y_6225_ = v___y_6251_;
                    v___y_6226_ = v___y_6253_;
                    v___y_6227_ = v___x_6269_;
                    state = 26;
                    continue;
                }
            }
            28 => {
                lean_inc_ref(v___y_6290_);
                v___x_6294_ = l_Array_append___redArg(v___y_6290_, v___y_6293_);
                lean_dec_ref(v___y_6293_);
                lean_inc(v___y_6274_);
                lean_inc(v___y_6278_);
                v___x_6295_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6295_, 0, v___y_6278_);
                lean_ctor_set(v___x_6295_, 1, v___y_6274_);
                lean_ctor_set(v___x_6295_, 2, v___x_6294_);
                if lean_obj_tag(v___y_6292_) == 1 {
                    v_val_6296_ = lean_ctor_get(v___y_6292_, 0);
                    v___x_6297_ = l_Lean_SourceInfo_fromRef(v_val_6296_, v___x_5714_);
                    v___x_6298_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_6299_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_6299_, 0, v___x_6297_);
                    lean_ctor_set(v___x_6299_, 1, v___x_6298_);
                    v___x_6300_ = l_Array_mkArray1___redArg(v___x_6299_);
                    v___y_6232_ = v___y_6271_;
                    v___y_6233_ = v___y_6272_;
                    v___y_6234_ = v___y_6273_;
                    v___y_6235_ = v___y_6274_;
                    v___y_6236_ = v___y_6275_;
                    v___y_6237_ = v___y_6276_;
                    v___y_6238_ = v___y_6277_;
                    v___y_6239_ = v___x_6295_;
                    v___y_6240_ = v___y_6279_;
                    v___y_6241_ = v___y_6278_;
                    v___y_6242_ = v___y_6280_;
                    v___y_6243_ = v___y_6281_;
                    v___y_6244_ = v___y_6282_;
                    v___y_6245_ = v___y_6283_;
                    v___y_6246_ = v___y_6284_;
                    v___y_6247_ = v___y_6285_;
                    v___y_6248_ = v___y_6286_;
                    v___y_6249_ = v___y_6287_;
                    v___y_6250_ = v___y_6288_;
                    v___y_6251_ = v___y_6290_;
                    v___y_6252_ = v___y_6289_;
                    v___y_6253_ = v___y_6292_;
                    v___y_6254_ = v___y_6291_;
                    v___y_6255_ = v___x_6300_;
                    state = 27;
                    continue;
                } else {
                    v___x_6301_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_6232_ = v___y_6271_;
                    v___y_6233_ = v___y_6272_;
                    v___y_6234_ = v___y_6273_;
                    v___y_6235_ = v___y_6274_;
                    v___y_6236_ = v___y_6275_;
                    v___y_6237_ = v___y_6276_;
                    v___y_6238_ = v___y_6277_;
                    v___y_6239_ = v___x_6295_;
                    v___y_6240_ = v___y_6279_;
                    v___y_6241_ = v___y_6278_;
                    v___y_6242_ = v___y_6280_;
                    v___y_6243_ = v___y_6281_;
                    v___y_6244_ = v___y_6282_;
                    v___y_6245_ = v___y_6283_;
                    v___y_6246_ = v___y_6284_;
                    v___y_6247_ = v___y_6285_;
                    v___y_6248_ = v___y_6286_;
                    v___y_6249_ = v___y_6287_;
                    v___y_6250_ = v___y_6288_;
                    v___y_6251_ = v___y_6290_;
                    v___y_6252_ = v___y_6289_;
                    v___y_6253_ = v___y_6292_;
                    v___y_6254_ = v___y_6291_;
                    v___y_6255_ = v___x_6301_;
                    state = 27;
                    continue;
                }
            }
            29 => {
                v_ref_6321_ = lean_ctor_get(v___y_6316_, 5);
                v___x_6322_ = l_Lean_SourceInfo_fromRef(v_ref_6321_, v___y_6320_);
                v___x_6323_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
                lean_inc_ref(v___x_5717_);
                lean_inc_ref(v___x_5716_);
                lean_inc_ref(v___x_5715_);
                v___x_6324_ =
                    l_Lean_Name_mkStr4(v___x_5715_, v___x_5716_, v___x_5717_, v___x_6323_);
                v___x_6325_ = l_Lean_SourceInfo_fromRef(v_tk_5730_, v___x_5714_);
                v___x_6326_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6326_, 0, v___x_6325_);
                lean_ctor_set(v___x_6326_, 1, v___x_6323_);
                v___x_6327_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                v___x_6328_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                if lean_obj_tag(v___y_6305_) == 1 {
                    v_val_6329_ = lean_ctor_get(v___y_6305_, 0);
                    lean_inc(v_val_6329_);
                    v___x_6330_ = l_Array_mkArray1___redArg(v_val_6329_);
                    v___y_6271_ = v___y_6303_;
                    v___y_6272_ = v___x_6324_;
                    v___y_6273_ = v___y_6304_;
                    v___y_6274_ = v___x_6327_;
                    v___y_6275_ = v___y_6305_;
                    v___y_6276_ = v___y_6306_;
                    v___y_6277_ = v___y_6307_;
                    v___y_6278_ = v___x_6322_;
                    v___y_6279_ = v___y_6308_;
                    v___y_6280_ = v___y_6309_;
                    v___y_6281_ = v___x_6326_;
                    v___y_6282_ = v___y_6310_;
                    v___y_6283_ = v___y_6311_;
                    v___y_6284_ = v___y_6312_;
                    v___y_6285_ = v___y_6313_;
                    v___y_6286_ = v___y_6314_;
                    v___y_6287_ = v___y_6315_;
                    v___y_6288_ = v___y_6316_;
                    v___y_6289_ = v___y_6317_;
                    v___y_6290_ = v___x_6328_;
                    v___y_6291_ = v___y_6319_;
                    v___y_6292_ = v___y_6318_;
                    v___y_6293_ = v___x_6330_;
                    state = 28;
                    continue;
                } else {
                    v___x_6331_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_6271_ = v___y_6303_;
                    v___y_6272_ = v___x_6324_;
                    v___y_6273_ = v___y_6304_;
                    v___y_6274_ = v___x_6327_;
                    v___y_6275_ = v___y_6305_;
                    v___y_6276_ = v___y_6306_;
                    v___y_6277_ = v___y_6307_;
                    v___y_6278_ = v___x_6322_;
                    v___y_6279_ = v___y_6308_;
                    v___y_6280_ = v___y_6309_;
                    v___y_6281_ = v___x_6326_;
                    v___y_6282_ = v___y_6310_;
                    v___y_6283_ = v___y_6311_;
                    v___y_6284_ = v___y_6312_;
                    v___y_6285_ = v___y_6313_;
                    v___y_6286_ = v___y_6314_;
                    v___y_6287_ = v___y_6315_;
                    v___y_6288_ = v___y_6316_;
                    v___y_6289_ = v___y_6317_;
                    v___y_6290_ = v___x_6328_;
                    v___y_6291_ = v___y_6319_;
                    v___y_6292_ = v___y_6318_;
                    v___y_6293_ = v___x_6331_;
                    state = 28;
                    continue;
                }
            }
            30 => {
                if lean_obj_tag(v___y_6336_) == 0 {
                    v___x_6350_ = 0;
                    v___y_6303_ = v___y_6333_;
                    v___y_6304_ = v___y_6343_;
                    v___y_6305_ = v___y_6335_;
                    v___y_6306_ = v___y_6336_;
                    v___y_6307_ = v___y_6338_;
                    v___y_6308_ = v___y_6347_;
                    v___y_6309_ = v___y_6342_;
                    v___y_6310_ = v___y_6344_;
                    v___y_6311_ = v_argsArray_6341_;
                    v___y_6312_ = v___y_6339_;
                    v___y_6313_ = v___y_6349_;
                    v___y_6314_ = v___y_6345_;
                    v___y_6315_ = v___y_6334_;
                    v___y_6316_ = v___y_6348_;
                    v___y_6317_ = v___y_6337_;
                    v___y_6318_ = v___y_6340_;
                    v___y_6319_ = v___y_6346_;
                    v___y_6320_ = v___x_6350_;
                    state = 29;
                    continue;
                } else {
                    if v___y_6339_ == 0 {
                        v___y_6303_ = v___y_6333_;
                        v___y_6304_ = v___y_6343_;
                        v___y_6305_ = v___y_6335_;
                        v___y_6306_ = v___y_6336_;
                        v___y_6307_ = v___y_6338_;
                        v___y_6308_ = v___y_6347_;
                        v___y_6309_ = v___y_6342_;
                        v___y_6310_ = v___y_6344_;
                        v___y_6311_ = v_argsArray_6341_;
                        v___y_6312_ = v___y_6339_;
                        v___y_6313_ = v___y_6349_;
                        v___y_6314_ = v___y_6345_;
                        v___y_6315_ = v___y_6334_;
                        v___y_6316_ = v___y_6348_;
                        v___y_6317_ = v___y_6337_;
                        v___y_6318_ = v___y_6340_;
                        v___y_6319_ = v___y_6346_;
                        v___y_6320_ = v___y_6339_;
                        state = 29;
                        continue;
                    } else {
                        v_ref_6351_ = lean_ctor_get(v___y_6348_, 5);
                        v___x_6352_ = 0;
                        v___x_6353_ = l_Lean_SourceInfo_fromRef(v_ref_6351_, v___x_6352_);
                        v___x_6354_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
                        lean_inc_ref(v___x_5717_);
                        lean_inc_ref(v___x_5716_);
                        lean_inc_ref(v___x_5715_);
                        v___x_6355_ =
                            l_Lean_Name_mkStr4(v___x_5715_, v___x_5716_, v___x_5717_, v___x_6354_);
                        v___x_6356_ = l_Lean_SourceInfo_fromRef(v_tk_5730_, v___x_5714_);
                        v___x_6357_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11;
                        v___x_6358_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_6358_, 0, v___x_6356_);
                        lean_ctor_set(v___x_6358_, 1, v___x_6357_);
                        v___x_6359_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                        v___x_6360_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                        if lean_obj_tag(v___y_6335_) == 1 {
                            v_val_6361_ = lean_ctor_get(v___y_6335_, 0);
                            lean_inc(v_val_6361_);
                            v___x_6362_ = l_Array_mkArray1___redArg(v_val_6361_);
                            v___y_6170_ = v___y_6333_;
                            v___y_6171_ = v___y_6343_;
                            v___y_6172_ = v___y_6335_;
                            v___y_6173_ = v___y_6336_;
                            v___y_6174_ = v___y_6338_;
                            v___y_6175_ = v___y_6347_;
                            v___y_6176_ = v___y_6342_;
                            v___y_6177_ = v___x_6358_;
                            v___y_6178_ = v___y_6344_;
                            v___y_6179_ = v_argsArray_6341_;
                            v___y_6180_ = v___y_6339_;
                            v___y_6181_ = v___x_6353_;
                            v___y_6182_ = v___y_6349_;
                            v___y_6183_ = v___y_6345_;
                            v___y_6184_ = v___y_6334_;
                            v___y_6185_ = v___y_6348_;
                            v___y_6186_ = v___x_6359_;
                            v___y_6187_ = v___y_6337_;
                            v___y_6188_ = v___x_6360_;
                            v___y_6189_ = v___y_6346_;
                            v___y_6190_ = v___y_6340_;
                            v___y_6191_ = v___x_6355_;
                            v___y_6192_ = v___x_6362_;
                            state = 25;
                            continue;
                        } else {
                            v___x_6363_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                            v___y_6170_ = v___y_6333_;
                            v___y_6171_ = v___y_6343_;
                            v___y_6172_ = v___y_6335_;
                            v___y_6173_ = v___y_6336_;
                            v___y_6174_ = v___y_6338_;
                            v___y_6175_ = v___y_6347_;
                            v___y_6176_ = v___y_6342_;
                            v___y_6177_ = v___x_6358_;
                            v___y_6178_ = v___y_6344_;
                            v___y_6179_ = v_argsArray_6341_;
                            v___y_6180_ = v___y_6339_;
                            v___y_6181_ = v___x_6353_;
                            v___y_6182_ = v___y_6349_;
                            v___y_6183_ = v___y_6345_;
                            v___y_6184_ = v___y_6334_;
                            v___y_6185_ = v___y_6348_;
                            v___y_6186_ = v___x_6359_;
                            v___y_6187_ = v___y_6337_;
                            v___y_6188_ = v___x_6360_;
                            v___y_6189_ = v___y_6346_;
                            v___y_6190_ = v___y_6340_;
                            v___y_6191_ = v___x_6355_;
                            v___y_6192_ = v___x_6363_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            31 => {
                v___x_6383_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_6377_,
                    v___y_6378_,
                    v___y_6366_,
                    v___y_6372_,
                    v___y_6374_,
                );
                if lean_obj_tag(v___x_6383_) == 0 {
                    v_a_6384_ = lean_ctor_get(v___x_6383_, 0);
                    lean_inc(v_a_6384_);
                    lean_dec_ref_known(v___x_6383_, 1);
                    v___x_6385_ = l_Lean_LibrarySuggestions_select(
                        v_a_6384_,
                        v___y_6382_,
                        v___y_6378_,
                        v___y_6366_,
                        v___y_6372_,
                        v___y_6374_,
                    );
                    if lean_obj_tag(v___x_6385_) == 0 {
                        v_a_6386_ = lean_ctor_get(v___x_6385_, 0);
                        lean_inc(v_a_6386_);
                        lean_dec_ref_known(v___x_6385_, 1);
                        v_sz_6387_ = lean_array_size(v_a_6386_);
                        v___x_6388_ = 0usize;
                        v___x_6389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__3(v_a_6386_, v_sz_6387_, v___x_6388_, v___y_6373_, v___y_6376_, v___y_6377_, v___y_6370_, v___y_6379_, v___y_6378_, v___y_6366_, v___y_6372_, v___y_6374_);
                        lean_dec(v_a_6386_);
                        if lean_obj_tag(v___x_6389_) == 0 {
                            v_a_6390_ = lean_ctor_get(v___x_6389_, 0);
                            lean_inc(v_a_6390_);
                            lean_dec_ref_known(v___x_6389_, 1);
                            v___y_6333_ = v___y_6365_;
                            v___y_6334_ = v___y_6375_;
                            v___y_6335_ = v___y_6367_;
                            v___y_6336_ = v___y_6369_;
                            v___y_6337_ = v___y_6380_;
                            v___y_6338_ = v___y_6368_;
                            v___y_6339_ = v___y_6371_;
                            v___y_6340_ = v___y_6381_;
                            v_argsArray_6341_ = v_a_6390_;
                            v___y_6342_ = v___y_6376_;
                            v___y_6343_ = v___y_6377_;
                            v___y_6344_ = v___y_6370_;
                            v___y_6345_ = v___y_6379_;
                            v___y_6346_ = v___y_6378_;
                            v___y_6347_ = v___y_6366_;
                            v___y_6348_ = v___y_6372_;
                            v___y_6349_ = v___y_6374_;
                            state = 30;
                            continue;
                        } else {
                            lean_dec(v___y_6381_);
                            lean_dec(v___y_6375_);
                            lean_dec(v___y_6369_);
                            lean_dec(v___y_6368_);
                            lean_dec(v___y_6367_);
                            lean_dec(v___y_6365_);
                            lean_dec(v_tk_5730_);
                            lean_dec_ref(v___x_5717_);
                            lean_dec_ref(v___x_5716_);
                            lean_dec_ref(v___x_5715_);
                            v_a_6391_ = lean_ctor_get(v___x_6389_, 0);
                            v_isSharedCheck_6398_ = (!lean_is_exclusive(v___x_6389_)) as u8;
                            if v_isSharedCheck_6398_ == 0 {
                                v___x_6393_ = v___x_6389_;
                                v_isShared_6394_ = v_isSharedCheck_6398_;
                                state = 32;
                                continue;
                            } else {
                                lean_inc(v_a_6391_);
                                lean_dec(v___x_6389_);
                                v___x_6393_ = lean_box(0);
                                v_isShared_6394_ = v_isSharedCheck_6398_;
                                state = 32;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_6381_);
                        lean_dec(v___y_6375_);
                        lean_dec_ref(v___y_6373_);
                        lean_dec(v___y_6369_);
                        lean_dec(v___y_6368_);
                        lean_dec(v___y_6367_);
                        lean_dec(v___y_6365_);
                        lean_dec(v_tk_5730_);
                        lean_dec_ref(v___x_5717_);
                        lean_dec_ref(v___x_5716_);
                        lean_dec_ref(v___x_5715_);
                        v_a_6399_ = lean_ctor_get(v___x_6385_, 0);
                        v_isSharedCheck_6406_ = (!lean_is_exclusive(v___x_6385_)) as u8;
                        if v_isSharedCheck_6406_ == 0 {
                            v___x_6401_ = v___x_6385_;
                            v_isShared_6402_ = v_isSharedCheck_6406_;
                            state = 34;
                            continue;
                        } else {
                            lean_inc(v_a_6399_);
                            lean_dec(v___x_6385_);
                            v___x_6401_ = lean_box(0);
                            v_isShared_6402_ = v_isSharedCheck_6406_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6382_);
                    lean_dec(v___y_6381_);
                    lean_dec(v___y_6375_);
                    lean_dec_ref(v___y_6373_);
                    lean_dec(v___y_6369_);
                    lean_dec(v___y_6368_);
                    lean_dec(v___y_6367_);
                    lean_dec(v___y_6365_);
                    lean_dec(v_tk_5730_);
                    lean_dec_ref(v___x_5717_);
                    lean_dec_ref(v___x_5716_);
                    lean_dec_ref(v___x_5715_);
                    v_a_6407_ = lean_ctor_get(v___x_6383_, 0);
                    v_isSharedCheck_6414_ = (!lean_is_exclusive(v___x_6383_)) as u8;
                    if v_isSharedCheck_6414_ == 0 {
                        v___x_6409_ = v___x_6383_;
                        v_isShared_6410_ = v_isSharedCheck_6414_;
                        state = 36;
                        continue;
                    } else {
                        lean_inc(v_a_6407_);
                        lean_dec(v___x_6383_);
                        v___x_6409_ = lean_box(0);
                        v_isShared_6410_ = v_isSharedCheck_6414_;
                        state = 36;
                        continue;
                    }
                }
            }
            32 => {
                if v_isShared_6394_ == 0 {
                    v___x_6396_ = v___x_6393_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6397_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6397_, 0, v_a_6391_);
                    v___x_6396_ = v_reuseFailAlloc_6397_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_6396_;
            }
            34 => {
                if v_isShared_6402_ == 0 {
                    v___x_6404_ = v___x_6401_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_6405_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6405_, 0, v_a_6399_);
                    v___x_6404_ = v_reuseFailAlloc_6405_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_6404_;
            }
            36 => {
                if v_isShared_6410_ == 0 {
                    v___x_6412_ = v___x_6409_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_6413_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6413_, 0, v_a_6407_);
                    v___x_6412_ = v_reuseFailAlloc_6413_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_6412_;
            }
            38 => {
                v_config_6434_ = lean_ctor_get(v___y_6427_, 0);
                lean_inc_ref(v_config_6434_);
                lean_dec_ref(v___y_6427_);
                v_suggestions_6435_ = lean_ctor_get_uint8(
                    v_config_6434_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 26) as u32,
                );
                if v_suggestions_6435_ == 0 {
                    lean_dec_ref(v_config_6434_);
                    lean_dec_ref(v___f_5718_);
                    v___y_6333_ = v___y_6416_;
                    v___y_6334_ = v___y_6425_;
                    v___y_6335_ = v___y_6418_;
                    v___y_6336_ = v___y_6420_;
                    v___y_6337_ = v___y_6431_;
                    v___y_6338_ = v___y_6419_;
                    v___y_6339_ = v___y_6422_;
                    v___y_6340_ = v___y_6432_;
                    v_argsArray_6341_ = v___y_6433_;
                    v___y_6342_ = v___y_6426_;
                    v___y_6343_ = v___y_6428_;
                    v___y_6344_ = v___y_6421_;
                    v___y_6345_ = v___y_6430_;
                    v___y_6346_ = v___y_6429_;
                    v___y_6347_ = v___y_6417_;
                    v___y_6348_ = v___y_6423_;
                    v___y_6349_ = v___y_6424_;
                    state = 30;
                    continue;
                } else {
                    v_maxSuggestions_6436_ = lean_ctor_get(v_config_6434_, 2);
                    lean_inc(v_maxSuggestions_6436_);
                    lean_dec_ref(v_config_6434_);
                    v___x_6437_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12;
                    v___x_6438_ = lean_box(0);
                    if lean_obj_tag(v_maxSuggestions_6436_) == 0 {
                        v___x_6439_ = lean_unsigned_to_nat(100);
                        v___x_6440_ = lean_alloc_ctor(0, 4, (0) as u32);
                        lean_ctor_set(v___x_6440_, 0, v___x_6439_);
                        lean_ctor_set(v___x_6440_, 1, v___x_6437_);
                        lean_ctor_set(v___x_6440_, 2, v___f_5718_);
                        lean_ctor_set(v___x_6440_, 3, v___x_6438_);
                        v___y_6365_ = v___y_6416_;
                        v___y_6366_ = v___y_6417_;
                        v___y_6367_ = v___y_6418_;
                        v___y_6368_ = v___y_6419_;
                        v___y_6369_ = v___y_6420_;
                        v___y_6370_ = v___y_6421_;
                        v___y_6371_ = v___y_6422_;
                        v___y_6372_ = v___y_6423_;
                        v___y_6373_ = v___y_6433_;
                        v___y_6374_ = v___y_6424_;
                        v___y_6375_ = v___y_6425_;
                        v___y_6376_ = v___y_6426_;
                        v___y_6377_ = v___y_6428_;
                        v___y_6378_ = v___y_6429_;
                        v___y_6379_ = v___y_6430_;
                        v___y_6380_ = v___y_6431_;
                        v___y_6381_ = v___y_6432_;
                        v___y_6382_ = v___x_6440_;
                        state = 31;
                        continue;
                    } else {
                        v_val_6441_ = lean_ctor_get(v_maxSuggestions_6436_, 0);
                        lean_inc(v_val_6441_);
                        lean_dec_ref_known(v_maxSuggestions_6436_, 1);
                        v___x_6442_ = lean_alloc_ctor(0, 4, (0) as u32);
                        lean_ctor_set(v___x_6442_, 0, v_val_6441_);
                        lean_ctor_set(v___x_6442_, 1, v___x_6437_);
                        lean_ctor_set(v___x_6442_, 2, v___f_5718_);
                        lean_ctor_set(v___x_6442_, 3, v___x_6438_);
                        v___y_6365_ = v___y_6416_;
                        v___y_6366_ = v___y_6417_;
                        v___y_6367_ = v___y_6418_;
                        v___y_6368_ = v___y_6419_;
                        v___y_6369_ = v___y_6420_;
                        v___y_6370_ = v___y_6421_;
                        v___y_6371_ = v___y_6422_;
                        v___y_6372_ = v___y_6423_;
                        v___y_6373_ = v___y_6433_;
                        v___y_6374_ = v___y_6424_;
                        v___y_6375_ = v___y_6425_;
                        v___y_6376_ = v___y_6426_;
                        v___y_6377_ = v___y_6428_;
                        v___y_6378_ = v___y_6429_;
                        v___y_6379_ = v___y_6430_;
                        v___y_6380_ = v___y_6431_;
                        v___y_6381_ = v___y_6432_;
                        v___y_6382_ = v___x_6442_;
                        state = 31;
                        continue;
                    }
                }
            }
            39 => {
                v___x_6459_ = 0;
                lean_inc(v___y_6454_);
                v___x_6460_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(
                    v___y_6454_,
                    v___x_6459_,
                    v___y_6446_,
                    v___y_6449_,
                    v___y_6451_,
                );
                if lean_obj_tag(v___x_6460_) == 0 {
                    if lean_obj_tag(v___y_6456_) == 1 {
                        v_a_6461_ = lean_ctor_get(v___x_6460_, 0);
                        lean_inc(v_a_6461_);
                        lean_dec_ref_known(v___x_6460_, 1);
                        v_val_6462_ = lean_ctor_get(v___y_6456_, 0);
                        lean_inc(v_val_6462_);
                        lean_dec_ref_known(v___y_6456_, 1);
                        v___x_6463_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_6462_);
                        lean_dec(v_val_6462_);
                        lean_inc(v___y_6450_);
                        v___y_6416_ = v___y_6450_;
                        v___y_6417_ = v___y_6457_;
                        v___y_6418_ = v___y_6458_;
                        v___y_6419_ = v___y_6454_;
                        v___y_6420_ = v___y_6447_;
                        v___y_6421_ = v___y_6448_;
                        v___y_6422_ = v___y_6444_;
                        v___y_6423_ = v___y_6449_;
                        v___y_6424_ = v___y_6451_;
                        v___y_6425_ = v___y_6450_;
                        v___y_6426_ = v___y_6446_;
                        v___y_6427_ = v_a_6461_;
                        v___y_6428_ = v___y_6453_;
                        v___y_6429_ = v___y_6452_;
                        v___y_6430_ = v___y_6455_;
                        v___y_6431_ = v___x_6459_;
                        v___y_6432_ = v___y_6445_;
                        v___y_6433_ = v___x_6463_;
                        state = 38;
                        continue;
                    } else {
                        lean_dec(v___y_6456_);
                        v_a_6464_ = lean_ctor_get(v___x_6460_, 0);
                        lean_inc(v_a_6464_);
                        lean_dec_ref_known(v___x_6460_, 1);
                        v___x_6465_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0;
                        lean_inc(v___y_6450_);
                        v___y_6416_ = v___y_6450_;
                        v___y_6417_ = v___y_6457_;
                        v___y_6418_ = v___y_6458_;
                        v___y_6419_ = v___y_6454_;
                        v___y_6420_ = v___y_6447_;
                        v___y_6421_ = v___y_6448_;
                        v___y_6422_ = v___y_6444_;
                        v___y_6423_ = v___y_6449_;
                        v___y_6424_ = v___y_6451_;
                        v___y_6425_ = v___y_6450_;
                        v___y_6426_ = v___y_6446_;
                        v___y_6427_ = v_a_6464_;
                        v___y_6428_ = v___y_6453_;
                        v___y_6429_ = v___y_6452_;
                        v___y_6430_ = v___y_6455_;
                        v___y_6431_ = v___x_6459_;
                        v___y_6432_ = v___y_6445_;
                        v___y_6433_ = v___x_6465_;
                        state = 38;
                        continue;
                    }
                } else {
                    lean_dec(v___y_6458_);
                    lean_dec(v___y_6456_);
                    lean_dec(v___y_6454_);
                    lean_dec(v___y_6450_);
                    lean_dec(v___y_6447_);
                    lean_dec(v___y_6445_);
                    lean_dec(v_tk_5730_);
                    lean_dec_ref(v___f_5718_);
                    lean_dec_ref(v___x_5717_);
                    lean_dec_ref(v___x_5716_);
                    lean_dec_ref(v___x_5715_);
                    v_a_6466_ = lean_ctor_get(v___x_6460_, 0);
                    v_isSharedCheck_6473_ = (!lean_is_exclusive(v___x_6460_)) as u8;
                    if v_isSharedCheck_6473_ == 0 {
                        v___x_6468_ = v___x_6460_;
                        v_isShared_6469_ = v_isSharedCheck_6473_;
                        state = 40;
                        continue;
                    } else {
                        lean_inc(v_a_6466_);
                        lean_dec(v___x_6460_);
                        v___x_6468_ = lean_box(0);
                        v_isShared_6469_ = v_isSharedCheck_6473_;
                        state = 40;
                        continue;
                    }
                }
            }
            40 => {
                if v_isShared_6469_ == 0 {
                    v___x_6471_ = v___x_6468_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_6472_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6472_, 0, v_a_6466_);
                    v___x_6471_ = v_reuseFailAlloc_6472_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_6471_;
            }
            42 => {
                v___x_6490_ = l_Lean_Syntax_getOptional_x3f(v___y_6482_);
                lean_dec(v___y_6482_);
                if lean_obj_tag(v___x_6490_) == 0 {
                    v___x_6491_ = lean_box(0);
                    v___y_6444_ = v___y_6479_;
                    v___y_6445_ = v___y_6488_;
                    v___y_6446_ = v___y_6484_;
                    v___y_6447_ = v___y_6476_;
                    v___y_6448_ = v___y_6478_;
                    v___y_6449_ = v___y_6480_;
                    v___y_6450_ = v___y_6489_;
                    v___y_6451_ = v___y_6483_;
                    v___y_6452_ = v___y_6486_;
                    v___y_6453_ = v___y_6485_;
                    v___y_6454_ = v___y_6477_;
                    v___y_6455_ = v___y_6487_;
                    v___y_6456_ = v___y_6481_;
                    v___y_6457_ = v___y_6475_;
                    v___y_6458_ = v___x_6491_;
                    state = 39;
                    continue;
                } else {
                    v_val_6492_ = lean_ctor_get(v___x_6490_, 0);
                    v_isSharedCheck_6499_ = (!lean_is_exclusive(v___x_6490_)) as u8;
                    if v_isSharedCheck_6499_ == 0 {
                        v___x_6494_ = v___x_6490_;
                        v_isShared_6495_ = v_isSharedCheck_6499_;
                        state = 43;
                        continue;
                    } else {
                        lean_inc(v_val_6492_);
                        lean_dec(v___x_6490_);
                        v___x_6494_ = lean_box(0);
                        v_isShared_6495_ = v_isSharedCheck_6499_;
                        state = 43;
                        continue;
                    }
                }
            }
            43 => {
                if v_isShared_6495_ == 0 {
                    v___x_6497_ = v___x_6494_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_6498_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6498_, 0, v_val_6492_);
                    v___x_6497_ = v_reuseFailAlloc_6498_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___y_6444_ = v___y_6479_;
                v___y_6445_ = v___y_6488_;
                v___y_6446_ = v___y_6484_;
                v___y_6447_ = v___y_6476_;
                v___y_6448_ = v___y_6478_;
                v___y_6449_ = v___y_6480_;
                v___y_6450_ = v___y_6489_;
                v___y_6451_ = v___y_6483_;
                v___y_6452_ = v___y_6486_;
                v___y_6453_ = v___y_6485_;
                v___y_6454_ = v___y_6477_;
                v___y_6455_ = v___y_6487_;
                v___y_6456_ = v___y_6481_;
                v___y_6457_ = v___y_6475_;
                v___y_6458_ = v___x_6497_;
                state = 39;
                continue;
            }
            45 => {
                v___x_6516_ = lean_unsigned_to_nat(4);
                v___x_6517_ = l_Lean_Syntax_getArg(v___y_6503_, v___x_6516_);
                lean_dec(v___y_6503_);
                v___x_6518_ = l_Lean_Syntax_getOptional_x3f(v___x_6517_);
                lean_dec(v___x_6517_);
                if lean_obj_tag(v___x_6518_) == 0 {
                    v___x_6519_ = lean_box(0);
                    v___y_6475_ = v___y_6513_;
                    v___y_6476_ = v___y_6502_;
                    v___y_6477_ = v___y_6501_;
                    v___y_6478_ = v___y_6510_;
                    v___y_6479_ = v___y_6504_;
                    v___y_6480_ = v___y_6514_;
                    v___y_6481_ = v_args_6507_;
                    v___y_6482_ = v___y_6506_;
                    v___y_6483_ = v___y_6515_;
                    v___y_6484_ = v___y_6508_;
                    v___y_6485_ = v___y_6509_;
                    v___y_6486_ = v___y_6512_;
                    v___y_6487_ = v___y_6511_;
                    v___y_6488_ = v___y_6505_;
                    v___y_6489_ = v___x_6519_;
                    state = 42;
                    continue;
                } else {
                    v_val_6520_ = lean_ctor_get(v___x_6518_, 0);
                    v_isSharedCheck_6527_ = (!lean_is_exclusive(v___x_6518_)) as u8;
                    if v_isSharedCheck_6527_ == 0 {
                        v___x_6522_ = v___x_6518_;
                        v_isShared_6523_ = v_isSharedCheck_6527_;
                        state = 46;
                        continue;
                    } else {
                        lean_inc(v_val_6520_);
                        lean_dec(v___x_6518_);
                        v___x_6522_ = lean_box(0);
                        v_isShared_6523_ = v_isSharedCheck_6527_;
                        state = 46;
                        continue;
                    }
                }
            }
            46 => {
                if v_isShared_6523_ == 0 {
                    v___x_6525_ = v___x_6522_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_6526_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6526_, 0, v_val_6520_);
                    v___x_6525_ = v_reuseFailAlloc_6526_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                v___y_6475_ = v___y_6513_;
                v___y_6476_ = v___y_6502_;
                v___y_6477_ = v___y_6501_;
                v___y_6478_ = v___y_6510_;
                v___y_6479_ = v___y_6504_;
                v___y_6480_ = v___y_6514_;
                v___y_6481_ = v_args_6507_;
                v___y_6482_ = v___y_6506_;
                v___y_6483_ = v___y_6515_;
                v___y_6484_ = v___y_6508_;
                v___y_6485_ = v___y_6509_;
                v___y_6486_ = v___y_6512_;
                v___y_6487_ = v___y_6511_;
                v___y_6488_ = v___y_6505_;
                v___y_6489_ = v___x_6525_;
                state = 42;
                continue;
            }
            48 => {
                v___x_6544_ = lean_unsigned_to_nat(3);
                v___x_6545_ = l_Lean_Syntax_getArg(v___y_6532_, v___x_6544_);
                v___x_6546_ = l_Lean_Syntax_isNone(v___x_6545_);
                if v___x_6546_ == 0 {
                    lean_inc(v___x_6545_);
                    v___x_6547_ = l_Lean_Syntax_matchesNull(v___x_6545_, v___x_6528_);
                    if v___x_6547_ == 0 {
                        lean_dec(v___x_6545_);
                        lean_dec(v_o_6535_);
                        lean_dec(v___y_6534_);
                        lean_dec(v___y_6532_);
                        lean_dec(v___y_6531_);
                        lean_dec(v___y_6530_);
                        lean_dec(v_tk_5730_);
                        lean_dec_ref(v___f_5718_);
                        lean_dec_ref(v___x_5717_);
                        lean_dec_ref(v___x_5716_);
                        lean_dec_ref(v___x_5715_);
                        v___x_6548_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                        return v___x_6548_;
                    } else {
                        v___x_6549_ = l_Lean_Syntax_getArg(v___x_6545_, v___x_5729_);
                        lean_dec(v___x_6545_);
                        v___x_6550_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13;
                        lean_inc_ref(v___x_5717_);
                        lean_inc_ref(v___x_5716_);
                        lean_inc_ref(v___x_5715_);
                        v___x_6551_ =
                            l_Lean_Name_mkStr4(v___x_5715_, v___x_5716_, v___x_5717_, v___x_6550_);
                        lean_inc(v___x_6549_);
                        v___x_6552_ = l_Lean_Syntax_isOfKind(v___x_6549_, v___x_6551_);
                        lean_dec(v___x_6551_);
                        if v___x_6552_ == 0 {
                            lean_dec(v___x_6549_);
                            lean_dec(v_o_6535_);
                            lean_dec(v___y_6534_);
                            lean_dec(v___y_6532_);
                            lean_dec(v___y_6531_);
                            lean_dec(v___y_6530_);
                            lean_dec(v_tk_5730_);
                            lean_dec_ref(v___f_5718_);
                            lean_dec_ref(v___x_5717_);
                            lean_dec_ref(v___x_5716_);
                            lean_dec_ref(v___x_5715_);
                            v___x_6553_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                            return v___x_6553_;
                        } else {
                            v___x_6554_ = l_Lean_Syntax_getArg(v___x_6549_, v___x_6528_);
                            lean_dec(v___x_6549_);
                            v_args_6555_ = l_Lean_Syntax_getArgs(v___x_6554_);
                            lean_dec(v___x_6554_);
                            v___x_6556_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_6556_, 0, v_args_6555_);
                            v___y_6501_ = v___y_6531_;
                            v___y_6502_ = v___y_6530_;
                            v___y_6503_ = v___y_6532_;
                            v___y_6504_ = v___y_6533_;
                            v___y_6505_ = v_o_6535_;
                            v___y_6506_ = v___y_6534_;
                            v_args_6507_ = v___x_6556_;
                            v___y_6508_ = v___y_6536_;
                            v___y_6509_ = v___y_6537_;
                            v___y_6510_ = v___y_6538_;
                            v___y_6511_ = v___y_6539_;
                            v___y_6512_ = v___y_6540_;
                            v___y_6513_ = v___y_6541_;
                            v___y_6514_ = v___y_6542_;
                            v___y_6515_ = v___y_6543_;
                            state = 45;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_6545_);
                    v___x_6557_ = lean_box(0);
                    v___y_6501_ = v___y_6531_;
                    v___y_6502_ = v___y_6530_;
                    v___y_6503_ = v___y_6532_;
                    v___y_6504_ = v___y_6533_;
                    v___y_6505_ = v_o_6535_;
                    v___y_6506_ = v___y_6534_;
                    v_args_6507_ = v___x_6557_;
                    v___y_6508_ = v___y_6536_;
                    v___y_6509_ = v___y_6537_;
                    v___y_6510_ = v___y_6538_;
                    v___y_6511_ = v___y_6539_;
                    v___y_6512_ = v___y_6540_;
                    v___y_6513_ = v___y_6541_;
                    v___y_6514_ = v___y_6542_;
                    v___y_6515_ = v___y_6543_;
                    state = 45;
                    continue;
                }
            }
            49 => {
                v___x_6568_ = lean_unsigned_to_nat(2);
                v___x_6569_ = l_Lean_Syntax_getArg(v_stx_5713_, v___x_6568_);
                v___x_6570_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14;
                lean_inc_ref(v___x_5717_);
                lean_inc_ref(v___x_5716_);
                lean_inc_ref(v___x_5715_);
                v___x_6571_ =
                    l_Lean_Name_mkStr4(v___x_5715_, v___x_5716_, v___x_5717_, v___x_6570_);
                lean_inc(v___x_6569_);
                v___x_6572_ = l_Lean_Syntax_isOfKind(v___x_6569_, v___x_6571_);
                lean_dec(v___x_6571_);
                if v___x_6572_ == 0 {
                    lean_dec(v___x_6569_);
                    lean_dec(v_bang_6559_);
                    lean_dec(v_tk_5730_);
                    lean_dec_ref(v___f_5718_);
                    lean_dec_ref(v___x_5717_);
                    lean_dec_ref(v___x_5716_);
                    lean_dec_ref(v___x_5715_);
                    v___x_6573_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                    return v___x_6573_;
                } else {
                    v_cfg_6574_ = l_Lean_Syntax_getArg(v___x_6569_, v___x_5729_);
                    v___x_6575_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15;
                    lean_inc_ref(v___x_5717_);
                    lean_inc_ref(v___x_5716_);
                    lean_inc_ref(v___x_5715_);
                    v___x_6576_ =
                        l_Lean_Name_mkStr4(v___x_5715_, v___x_5716_, v___x_5717_, v___x_6575_);
                    lean_inc(v_cfg_6574_);
                    v___x_6577_ = l_Lean_Syntax_isOfKind(v_cfg_6574_, v___x_6576_);
                    lean_dec(v___x_6576_);
                    if v___x_6577_ == 0 {
                        lean_dec(v_cfg_6574_);
                        lean_dec(v___x_6569_);
                        lean_dec(v_bang_6559_);
                        lean_dec(v_tk_5730_);
                        lean_dec_ref(v___f_5718_);
                        lean_dec_ref(v___x_5717_);
                        lean_dec_ref(v___x_5716_);
                        lean_dec_ref(v___x_5715_);
                        v___x_6578_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                        return v___x_6578_;
                    } else {
                        v___x_6579_ = l_Lean_Syntax_getArg(v___x_6569_, v___x_6528_);
                        v___x_6580_ = l_Lean_Syntax_getArg(v___x_6569_, v___x_6568_);
                        v___x_6581_ = l_Lean_Syntax_isNone(v___x_6580_);
                        if v___x_6581_ == 0 {
                            lean_inc(v___x_6580_);
                            v___x_6582_ = l_Lean_Syntax_matchesNull(v___x_6580_, v___x_6528_);
                            if v___x_6582_ == 0 {
                                lean_dec(v___x_6580_);
                                lean_dec(v___x_6579_);
                                lean_dec(v_cfg_6574_);
                                lean_dec(v___x_6569_);
                                lean_dec(v_bang_6559_);
                                lean_dec(v_tk_5730_);
                                lean_dec_ref(v___f_5718_);
                                lean_dec_ref(v___x_5717_);
                                lean_dec_ref(v___x_5716_);
                                lean_dec_ref(v___x_5715_);
                                v___x_6583_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                                return v___x_6583_;
                            } else {
                                v_o_6584_ = l_Lean_Syntax_getArg(v___x_6580_, v___x_5729_);
                                lean_dec(v___x_6580_);
                                v___x_6585_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_6585_, 0, v_o_6584_);
                                v___y_6530_ = v_bang_6559_;
                                v___y_6531_ = v_cfg_6574_;
                                v___y_6532_ = v___x_6569_;
                                v___y_6533_ = v___x_6577_;
                                v___y_6534_ = v___x_6579_;
                                v_o_6535_ = v___x_6585_;
                                v___y_6536_ = v___y_6560_;
                                v___y_6537_ = v___y_6561_;
                                v___y_6538_ = v___y_6562_;
                                v___y_6539_ = v___y_6563_;
                                v___y_6540_ = v___y_6564_;
                                v___y_6541_ = v___y_6565_;
                                v___y_6542_ = v___y_6566_;
                                v___y_6543_ = v___y_6567_;
                                state = 48;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_6580_);
                            v___x_6586_ = lean_box(0);
                            v___y_6530_ = v_bang_6559_;
                            v___y_6531_ = v_cfg_6574_;
                            v___y_6532_ = v___x_6569_;
                            v___y_6533_ = v___x_6577_;
                            v___y_6534_ = v___x_6579_;
                            v_o_6535_ = v___x_6586_;
                            v___y_6536_ = v___y_6560_;
                            v___y_6537_ = v___y_6561_;
                            v___y_6538_ = v___y_6562_;
                            v___y_6539_ = v___y_6563_;
                            v___y_6540_ = v___y_6564_;
                            v___y_6541_ = v___y_6565_;
                            v___y_6542_ = v___y_6566_;
                            v___y_6543_ = v___y_6567_;
                            state = 48;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(
    mut v___x_6594_: *mut LeanObject,
    mut v_stx_6595_: *mut LeanObject,
    mut v___x_6596_: *mut LeanObject,
    mut v___x_6597_: *mut LeanObject,
    mut v___x_6598_: *mut LeanObject,
    mut v___x_6599_: *mut LeanObject,
    mut v___f_6600_: *mut LeanObject,
    mut v___y_6601_: *mut LeanObject,
    mut v___y_6602_: *mut LeanObject,
    mut v___y_6603_: *mut LeanObject,
    mut v___y_6604_: *mut LeanObject,
    mut v___y_6605_: *mut LeanObject,
    mut v___y_6606_: *mut LeanObject,
    mut v___y_6607_: *mut LeanObject,
    mut v___y_6608_: *mut LeanObject,
    mut v___y_6609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_40466__boxed_6610_: u8 = 0;
    let mut v___x_40467__boxed_6611_: u8 = 0;
    let mut v_res_6612_: *mut LeanObject = core::ptr::null_mut();
    v___x_40466__boxed_6610_ = (lean_unbox(v___x_6594_) as u8);
    v___x_40467__boxed_6611_ = (lean_unbox(v___x_6596_) as u8);
    v_res_6612_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(
        v___x_40466__boxed_6610_,
        v_stx_6595_,
        v___x_40467__boxed_6611_,
        v___x_6597_,
        v___x_6598_,
        v___x_6599_,
        v___f_6600_,
        v___y_6601_,
        v___y_6602_,
        v___y_6603_,
        v___y_6604_,
        v___y_6605_,
        v___y_6606_,
        v___y_6607_,
        v___y_6608_,
    );
    lean_dec(v___y_6608_);
    lean_dec_ref(v___y_6607_);
    lean_dec(v___y_6606_);
    lean_dec_ref(v___y_6605_);
    lean_dec(v___y_6604_);
    lean_dec_ref(v___y_6603_);
    lean_dec(v___y_6602_);
    lean_dec_ref(v___y_6601_);
    lean_dec(v_stx_6595_);
    return v_res_6612_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpTrace(
    mut v_stx_6622_: *mut LeanObject,
    mut v_a_6623_: *mut LeanObject,
    mut v_a_6624_: *mut LeanObject,
    mut v_a_6625_: *mut LeanObject,
    mut v_a_6626_: *mut LeanObject,
    mut v_a_6627_: *mut LeanObject,
    mut v_a_6628_: *mut LeanObject,
    mut v_a_6629_: *mut LeanObject,
    mut v_a_6630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: u8 = 0;
    let mut v___x_6637_: u8 = 0;
    let mut v___f_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut LeanObject = core::ptr::null_mut();
    v___x_6632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0;
    v___x_6633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1;
    v___x_6634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2;
    v___x_6635_ = l_Lean_Elab_Tactic_evalSimpTrace___closed__1;
    lean_inc(v_stx_6622_);
    v___x_6636_ = l_Lean_Syntax_isOfKind(v_stx_6622_, v___x_6635_);
    v___x_6637_ = 1;
    v___f_6638_ = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
    v___x_6639_ = lean_box((v___x_6636_) as usize);
    v___x_6640_ = lean_box((v___x_6637_) as usize);
    v___y_6641_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed as *mut core::ffi::c_void,
        16,
        7,
    );
    lean_closure_set(v___y_6641_, 0, v___x_6639_);
    lean_closure_set(v___y_6641_, 1, v_stx_6622_);
    lean_closure_set(v___y_6641_, 2, v___x_6640_);
    lean_closure_set(v___y_6641_, 3, v___x_6632_);
    lean_closure_set(v___y_6641_, 4, v___x_6633_);
    lean_closure_set(v___y_6641_, 5, v___x_6634_);
    lean_closure_set(v___y_6641_, 6, v___f_6638_);
    v___x_6642_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_withSimpDiagnostics___boxed as *mut core::ffi::c_void,
        10,
        1,
    );
    lean_closure_set(v___x_6642_, 0, v___y_6641_);
    v___x_6643_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___x_6642_,
        v_a_6623_,
        v_a_6624_,
        v_a_6625_,
        v_a_6626_,
        v_a_6627_,
        v_a_6628_,
        v_a_6629_,
        v_a_6630_,
    );
    return v___x_6643_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpTrace___boxed(
    mut v_stx_6644_: *mut LeanObject,
    mut v_a_6645_: *mut LeanObject,
    mut v_a_6646_: *mut LeanObject,
    mut v_a_6647_: *mut LeanObject,
    mut v_a_6648_: *mut LeanObject,
    mut v_a_6649_: *mut LeanObject,
    mut v_a_6650_: *mut LeanObject,
    mut v_a_6651_: *mut LeanObject,
    mut v_a_6652_: *mut LeanObject,
    mut v_a_6653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6654_: *mut LeanObject = core::ptr::null_mut();
    v_res_6654_ = l_Lean_Elab_Tactic_evalSimpTrace(
        v_stx_6644_,
        v_a_6645_,
        v_a_6646_,
        v_a_6647_,
        v_a_6648_,
        v_a_6649_,
        v_a_6650_,
        v_a_6651_,
        v_a_6652_,
    );
    lean_dec(v_a_6652_);
    lean_dec_ref(v_a_6651_);
    lean_dec(v_a_6650_);
    lean_dec_ref(v_a_6649_);
    lean_dec(v_a_6648_);
    lean_dec_ref(v_a_6647_);
    lean_dec(v_a_6646_);
    lean_dec_ref(v_a_6645_);
    return v_res_6654_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(
    mut v___x_6655_: *mut LeanObject,
    mut v_as_6656_: *mut LeanObject,
    mut v_as_x27_6657_: *mut LeanObject,
    mut v_b_6658_: *mut LeanObject,
    mut v_a_6659_: *mut LeanObject,
    mut v___y_6660_: *mut LeanObject,
    mut v___y_6661_: *mut LeanObject,
    mut v___y_6662_: *mut LeanObject,
    mut v___y_6663_: *mut LeanObject,
    mut v___y_6664_: *mut LeanObject,
    mut v___y_6665_: *mut LeanObject,
    mut v___y_6666_: *mut LeanObject,
    mut v___y_6667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    v___x_6669_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg(
        v___x_6655_,
        v_as_x27_6657_,
        v_b_6658_,
        v___y_6666_,
    );
    return v___x_6669_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___boxed(
    mut v___x_6670_: *mut LeanObject,
    mut v_as_6671_: *mut LeanObject,
    mut v_as_x27_6672_: *mut LeanObject,
    mut v_b_6673_: *mut LeanObject,
    mut v_a_6674_: *mut LeanObject,
    mut v___y_6675_: *mut LeanObject,
    mut v___y_6676_: *mut LeanObject,
    mut v___y_6677_: *mut LeanObject,
    mut v___y_6678_: *mut LeanObject,
    mut v___y_6679_: *mut LeanObject,
    mut v___y_6680_: *mut LeanObject,
    mut v___y_6681_: *mut LeanObject,
    mut v___y_6682_: *mut LeanObject,
    mut v___y_6683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6684_: *mut LeanObject = core::ptr::null_mut();
    v_res_6684_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2(
        v___x_6670_,
        v_as_6671_,
        v_as_x27_6672_,
        v_b_6673_,
        v_a_6674_,
        v___y_6675_,
        v___y_6676_,
        v___y_6677_,
        v___y_6678_,
        v___y_6679_,
        v___y_6680_,
        v___y_6681_,
        v___y_6682_,
    );
    lean_dec(v___y_6682_);
    lean_dec_ref(v___y_6681_);
    lean_dec(v___y_6680_);
    lean_dec_ref(v___y_6679_);
    lean_dec(v___y_6678_);
    lean_dec_ref(v___y_6677_);
    lean_dec(v___y_6676_);
    lean_dec_ref(v___y_6675_);
    lean_dec(v_as_x27_6672_);
    lean_dec(v_as_6671_);
    lean_dec(v___x_6670_);
    return v_res_6684_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(
    mut v_00_u03b1_6685_: *mut LeanObject,
    mut v_ref_6686_: *mut LeanObject,
    mut v_msg_6687_: *mut LeanObject,
    mut v___y_6688_: *mut LeanObject,
    mut v___y_6689_: *mut LeanObject,
    mut v___y_6690_: *mut LeanObject,
    mut v___y_6691_: *mut LeanObject,
    mut v___y_6692_: *mut LeanObject,
    mut v___y_6693_: *mut LeanObject,
    mut v___y_6694_: *mut LeanObject,
    mut v___y_6695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6697_: *mut LeanObject = core::ptr::null_mut();
    v___x_6697_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___redArg(v_ref_6686_, v_msg_6687_, v___y_6688_, v___y_6689_, v___y_6690_, v___y_6691_, v___y_6692_, v___y_6693_, v___y_6694_, v___y_6695_);
    return v___x_6697_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b1_6698_: *mut LeanObject,
    mut v_ref_6699_: *mut LeanObject,
    mut v_msg_6700_: *mut LeanObject,
    mut v___y_6701_: *mut LeanObject,
    mut v___y_6702_: *mut LeanObject,
    mut v___y_6703_: *mut LeanObject,
    mut v___y_6704_: *mut LeanObject,
    mut v___y_6705_: *mut LeanObject,
    mut v___y_6706_: *mut LeanObject,
    mut v___y_6707_: *mut LeanObject,
    mut v___y_6708_: *mut LeanObject,
    mut v___y_6709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6710_: *mut LeanObject = core::ptr::null_mut();
    v_res_6710_ = l_Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6(v_00_u03b1_6698_, v_ref_6699_, v_msg_6700_, v___y_6701_, v___y_6702_, v___y_6703_, v___y_6704_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_);
    lean_dec(v___y_6708_);
    lean_dec_ref(v___y_6707_);
    lean_dec(v___y_6706_);
    lean_dec_ref(v___y_6705_);
    lean_dec(v___y_6704_);
    lean_dec_ref(v___y_6703_);
    lean_dec(v___y_6702_);
    lean_dec_ref(v___y_6701_);
    lean_dec(v_ref_6699_);
    return v_res_6710_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(
    mut v_00_u03b1_6711_: *mut LeanObject,
    mut v_ref_6712_: *mut LeanObject,
    mut v_constName_6713_: *mut LeanObject,
    mut v___y_6714_: *mut LeanObject,
    mut v___y_6715_: *mut LeanObject,
    mut v___y_6716_: *mut LeanObject,
    mut v___y_6717_: *mut LeanObject,
    mut v___y_6718_: *mut LeanObject,
    mut v___y_6719_: *mut LeanObject,
    mut v___y_6720_: *mut LeanObject,
    mut v___y_6721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6723_: *mut LeanObject = core::ptr::null_mut();
    v___x_6723_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___redArg(v_ref_6712_, v_constName_6713_, v___y_6714_, v___y_6715_, v___y_6716_, v___y_6717_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_);
    return v___x_6723_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10___boxed(
    mut v_00_u03b1_6724_: *mut LeanObject,
    mut v_ref_6725_: *mut LeanObject,
    mut v_constName_6726_: *mut LeanObject,
    mut v___y_6727_: *mut LeanObject,
    mut v___y_6728_: *mut LeanObject,
    mut v___y_6729_: *mut LeanObject,
    mut v___y_6730_: *mut LeanObject,
    mut v___y_6731_: *mut LeanObject,
    mut v___y_6732_: *mut LeanObject,
    mut v___y_6733_: *mut LeanObject,
    mut v___y_6734_: *mut LeanObject,
    mut v___y_6735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6736_: *mut LeanObject = core::ptr::null_mut();
    v_res_6736_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10(v_00_u03b1_6724_, v_ref_6725_, v_constName_6726_, v___y_6727_, v___y_6728_, v___y_6729_, v___y_6730_, v___y_6731_, v___y_6732_, v___y_6733_, v___y_6734_);
    lean_dec(v___y_6734_);
    lean_dec_ref(v___y_6733_);
    lean_dec(v___y_6732_);
    lean_dec_ref(v___y_6731_);
    lean_dec(v___y_6730_);
    lean_dec_ref(v___y_6729_);
    lean_dec(v___y_6728_);
    lean_dec_ref(v___y_6727_);
    lean_dec(v_ref_6725_);
    return v_res_6736_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(
    mut v_00_u03b1_6737_: *mut LeanObject,
    mut v_msg_6738_: *mut LeanObject,
    mut v___y_6739_: *mut LeanObject,
    mut v___y_6740_: *mut LeanObject,
    mut v___y_6741_: *mut LeanObject,
    mut v___y_6742_: *mut LeanObject,
    mut v___y_6743_: *mut LeanObject,
    mut v___y_6744_: *mut LeanObject,
    mut v___y_6745_: *mut LeanObject,
    mut v___y_6746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
    v___x_6748_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___redArg(v_msg_6738_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_);
    return v___x_6748_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14___boxed(
    mut v_00_u03b1_6749_: *mut LeanObject,
    mut v_msg_6750_: *mut LeanObject,
    mut v___y_6751_: *mut LeanObject,
    mut v___y_6752_: *mut LeanObject,
    mut v___y_6753_: *mut LeanObject,
    mut v___y_6754_: *mut LeanObject,
    mut v___y_6755_: *mut LeanObject,
    mut v___y_6756_: *mut LeanObject,
    mut v___y_6757_: *mut LeanObject,
    mut v___y_6758_: *mut LeanObject,
    mut v___y_6759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6760_: *mut LeanObject = core::ptr::null_mut();
    v_res_6760_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__2_spec__6_spec__14(v_00_u03b1_6749_, v_msg_6750_, v___y_6751_, v___y_6752_, v___y_6753_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_, v___y_6758_);
    lean_dec(v___y_6758_);
    lean_dec_ref(v___y_6757_);
    lean_dec(v___y_6756_);
    lean_dec_ref(v___y_6755_);
    lean_dec(v___y_6754_);
    lean_dec_ref(v___y_6753_);
    lean_dec(v___y_6752_);
    lean_dec_ref(v___y_6751_);
    return v_res_6760_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(
    mut v_opt_6761_: *mut LeanObject,
    mut v___y_6762_: *mut LeanObject,
    mut v___y_6763_: *mut LeanObject,
    mut v___y_6764_: *mut LeanObject,
    mut v___y_6765_: *mut LeanObject,
    mut v___y_6766_: *mut LeanObject,
    mut v___y_6767_: *mut LeanObject,
    mut v___y_6768_: *mut LeanObject,
    mut v___y_6769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
    v___x_6771_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___redArg(v_opt_6761_, v___y_6768_);
    return v___x_6771_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8___boxed(
    mut v_opt_6772_: *mut LeanObject,
    mut v___y_6773_: *mut LeanObject,
    mut v___y_6774_: *mut LeanObject,
    mut v___y_6775_: *mut LeanObject,
    mut v___y_6776_: *mut LeanObject,
    mut v___y_6777_: *mut LeanObject,
    mut v___y_6778_: *mut LeanObject,
    mut v___y_6779_: *mut LeanObject,
    mut v___y_6780_: *mut LeanObject,
    mut v___y_6781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6782_: *mut LeanObject = core::ptr::null_mut();
    v_res_6782_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__8(v_opt_6772_, v___y_6773_, v___y_6774_, v___y_6775_, v___y_6776_, v___y_6777_, v___y_6778_, v___y_6779_, v___y_6780_);
    lean_dec(v___y_6780_);
    lean_dec_ref(v___y_6779_);
    lean_dec(v___y_6778_);
    lean_dec_ref(v___y_6777_);
    lean_dec(v___y_6776_);
    lean_dec_ref(v___y_6775_);
    lean_dec(v___y_6774_);
    lean_dec_ref(v___y_6773_);
    lean_dec_ref(v_opt_6772_);
    return v_res_6782_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(
    mut v_00_u03b1_6783_: *mut LeanObject,
    mut v_ref_6784_: *mut LeanObject,
    mut v_msg_6785_: *mut LeanObject,
    mut v_declHint_6786_: *mut LeanObject,
    mut v___y_6787_: *mut LeanObject,
    mut v___y_6788_: *mut LeanObject,
    mut v___y_6789_: *mut LeanObject,
    mut v___y_6790_: *mut LeanObject,
    mut v___y_6791_: *mut LeanObject,
    mut v___y_6792_: *mut LeanObject,
    mut v___y_6793_: *mut LeanObject,
    mut v___y_6794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    v___x_6796_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___redArg(v_ref_6784_, v_msg_6785_, v_declHint_6786_, v___y_6787_, v___y_6788_, v___y_6789_, v___y_6790_, v___y_6791_, v___y_6792_, v___y_6793_, v___y_6794_);
    return v___x_6796_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14___boxed(
    mut v_00_u03b1_6797_: *mut LeanObject,
    mut v_ref_6798_: *mut LeanObject,
    mut v_msg_6799_: *mut LeanObject,
    mut v_declHint_6800_: *mut LeanObject,
    mut v___y_6801_: *mut LeanObject,
    mut v___y_6802_: *mut LeanObject,
    mut v___y_6803_: *mut LeanObject,
    mut v___y_6804_: *mut LeanObject,
    mut v___y_6805_: *mut LeanObject,
    mut v___y_6806_: *mut LeanObject,
    mut v___y_6807_: *mut LeanObject,
    mut v___y_6808_: *mut LeanObject,
    mut v___y_6809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6810_: *mut LeanObject = core::ptr::null_mut();
    v_res_6810_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14(v_00_u03b1_6797_, v_ref_6798_, v_msg_6799_, v_declHint_6800_, v___y_6801_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_);
    lean_dec(v___y_6808_);
    lean_dec_ref(v___y_6807_);
    lean_dec(v___y_6806_);
    lean_dec_ref(v___y_6805_);
    lean_dec(v___y_6804_);
    lean_dec_ref(v___y_6803_);
    lean_dec(v___y_6802_);
    lean_dec_ref(v___y_6801_);
    lean_dec(v_ref_6798_);
    return v_res_6810_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(
    mut v_msg_6811_: *mut LeanObject,
    mut v_declHint_6812_: *mut LeanObject,
    mut v___y_6813_: *mut LeanObject,
    mut v___y_6814_: *mut LeanObject,
    mut v___y_6815_: *mut LeanObject,
    mut v___y_6816_: *mut LeanObject,
    mut v___y_6817_: *mut LeanObject,
    mut v___y_6818_: *mut LeanObject,
    mut v___y_6819_: *mut LeanObject,
    mut v___y_6820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6822_: *mut LeanObject = core::ptr::null_mut();
    v___x_6822_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___redArg(v_msg_6811_, v_declHint_6812_, v___y_6820_);
    return v___x_6822_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23___boxed(
    mut v_msg_6823_: *mut LeanObject,
    mut v_declHint_6824_: *mut LeanObject,
    mut v___y_6825_: *mut LeanObject,
    mut v___y_6826_: *mut LeanObject,
    mut v___y_6827_: *mut LeanObject,
    mut v___y_6828_: *mut LeanObject,
    mut v___y_6829_: *mut LeanObject,
    mut v___y_6830_: *mut LeanObject,
    mut v___y_6831_: *mut LeanObject,
    mut v___y_6832_: *mut LeanObject,
    mut v___y_6833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6834_: *mut LeanObject = core::ptr::null_mut();
    v_res_6834_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__3_spec__10_spec__14_spec__19_spec__23(v_msg_6823_, v_declHint_6824_, v___y_6825_, v___y_6826_, v___y_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_);
    lean_dec(v___y_6832_);
    lean_dec_ref(v___y_6831_);
    lean_dec(v___y_6830_);
    lean_dec_ref(v___y_6829_);
    lean_dec(v___y_6828_);
    lean_dec_ref(v___y_6827_);
    lean_dec(v___y_6826_);
    lean_dec_ref(v___y_6825_);
    return v_res_6834_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(
    mut v_ref_6835_: *mut LeanObject,
    mut v_msgData_6836_: *mut LeanObject,
    mut v_severity_6837_: u8,
    mut v_isSilent_6838_: u8,
    mut v___y_6839_: *mut LeanObject,
    mut v___y_6840_: *mut LeanObject,
    mut v___y_6841_: *mut LeanObject,
    mut v___y_6842_: *mut LeanObject,
    mut v___y_6843_: *mut LeanObject,
    mut v___y_6844_: *mut LeanObject,
    mut v___y_6845_: *mut LeanObject,
    mut v___y_6846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6848_: *mut LeanObject = core::ptr::null_mut();
    v___x_6848_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___redArg(v_ref_6835_, v_msgData_6836_, v_severity_6837_, v_isSilent_6838_, v___y_6843_, v___y_6844_, v___y_6845_, v___y_6846_);
    return v___x_6848_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20___boxed(
    mut v_ref_6849_: *mut LeanObject,
    mut v_msgData_6850_: *mut LeanObject,
    mut v_severity_6851_: *mut LeanObject,
    mut v_isSilent_6852_: *mut LeanObject,
    mut v___y_6853_: *mut LeanObject,
    mut v___y_6854_: *mut LeanObject,
    mut v___y_6855_: *mut LeanObject,
    mut v___y_6856_: *mut LeanObject,
    mut v___y_6857_: *mut LeanObject,
    mut v___y_6858_: *mut LeanObject,
    mut v___y_6859_: *mut LeanObject,
    mut v___y_6860_: *mut LeanObject,
    mut v___y_6861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_6862_: u8 = 0;
    let mut v_isSilent_boxed_6863_: u8 = 0;
    let mut v_res_6864_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_6862_ = (lean_unbox(v_severity_6851_) as u8);
    v_isSilent_boxed_6863_ = (lean_unbox(v_isSilent_6852_) as u8);
    v_res_6864_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___00Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1_spec__1_spec__2_spec__6_spec__9_spec__14_spec__20(v_ref_6849_, v_msgData_6850_, v_severity_boxed_6862_, v_isSilent_boxed_6863_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_, v___y_6859_, v___y_6860_);
    lean_dec(v___y_6860_);
    lean_dec_ref(v___y_6859_);
    lean_dec(v___y_6858_);
    lean_dec_ref(v___y_6857_);
    lean_dec(v___y_6856_);
    lean_dec_ref(v___y_6855_);
    lean_dec(v___y_6854_);
    lean_dec_ref(v___y_6853_);
    lean_dec(v_ref_6849_);
    return v_res_6864_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1()
-> *mut LeanObject {
    let mut v___x_6872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
    v___x_6872_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_6873_ = l_Lean_Elab_Tactic_evalSimpTrace___closed__1;
    v___x_6874_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1;
    v___x_6875_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSimpTrace___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_6876_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6872_,
        v___x_6873_,
        v___x_6874_,
        v___x_6875_,
    );
    return v___x_6876_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___boxed(
    mut v_a_6877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6878_: *mut LeanObject = core::ptr::null_mut();
    v_res_6878_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
    return v_res_6878_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3()
-> *mut LeanObject {
    let mut v___x_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
    v___x_6905_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1;
    v___x_6906_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6;
    v___x_6907_ = l_Lean_addBuiltinDeclarationRanges(v___x_6905_, v___x_6906_);
    return v___x_6907_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___boxed(
    mut v_a_6908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6909_: *mut LeanObject = core::ptr::null_mut();
    v_res_6909_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
    return v_res_6909_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(
    mut v___x_6910_: *mut LeanObject,
    mut v_as_x27_6911_: *mut LeanObject,
    mut v_b_6912_: *mut LeanObject,
    mut v___y_6913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: u8 = 0;
    let mut v___x_6920_: u8 = 0;
    let mut v___x_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_6911_) == 0 {
                    v___x_6915_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6915_, 0, v_b_6912_);
                    return v___x_6915_;
                } else {
                    v_head_6916_ = lean_ctor_get(v_as_x27_6911_, 0);
                    v_tail_6917_ = lean_ctor_get(v_as_x27_6911_, 1);
                    v_ref_6918_ = lean_ctor_get(v___y_6913_, 5);
                    v___x_6919_ = 1;
                    v___x_6920_ = 0;
                    v___x_6921_ = l_Lean_SourceInfo_fromRef(v_ref_6918_, v___x_6920_);
                    v___x_6922_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__1;
                    v___x_6923_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                    v___x_6924_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                    lean_inc(v___x_6921_);
                    v___x_6925_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_6925_, 0, v___x_6921_);
                    lean_ctor_set(v___x_6925_, 1, v___x_6923_);
                    lean_ctor_set(v___x_6925_, 2, v___x_6924_);
                    lean_inc(v_head_6916_);
                    v___x_6926_ = l_Lean_mkCIdentFrom(v___x_6910_, v_head_6916_, v___x_6919_);
                    lean_inc_ref(v___x_6925_);
                    v___x_6927_ = l_Lean_Syntax_node3(
                        v___x_6921_,
                        v___x_6922_,
                        v___x_6925_,
                        v___x_6925_,
                        v___x_6926_,
                    );
                    v___x_6928_ = lean_array_push(v_b_6912_, v___x_6927_);
                    v_as_x27_6911_ = v_tail_6917_;
                    v_b_6912_ = v___x_6928_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg___boxed(
    mut v___x_6930_: *mut LeanObject,
    mut v_as_x27_6931_: *mut LeanObject,
    mut v_b_6932_: *mut LeanObject,
    mut v___y_6933_: *mut LeanObject,
    mut v___y_6934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6935_: *mut LeanObject = core::ptr::null_mut();
    v_res_6935_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(
        v___x_6930_,
        v_as_x27_6931_,
        v_b_6932_,
        v___y_6933_,
    );
    lean_dec_ref(v___y_6933_);
    lean_dec(v_as_x27_6931_);
    lean_dec(v___x_6930_);
    return v_res_6935_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(
    mut v_as_6936_: *mut LeanObject,
    mut v_sz_6937_: usize,
    mut v_i_6938_: usize,
    mut v_b_6939_: *mut LeanObject,
    mut v___y_6940_: *mut LeanObject,
    mut v___y_6941_: *mut LeanObject,
    mut v___y_6942_: *mut LeanObject,
    mut v___y_6943_: *mut LeanObject,
    mut v___y_6944_: *mut LeanObject,
    mut v___y_6945_: *mut LeanObject,
    mut v___y_6946_: *mut LeanObject,
    mut v___y_6947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6949_: u8 = 0;
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: usize = 0;
    let mut v___x_6959_: usize = 0;
    let mut v_a_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6964_: u8 = 0;
    let mut v___x_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6949_ = lean_usize_dec_lt(v_i_6938_, v_sz_6937_);
                if v___x_6949_ == 0 {
                    v___x_6950_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6950_, 0, v_b_6939_);
                    return v___x_6950_;
                } else {
                    v_a_6951_ = lean_array_uget_borrowed(v_as_6936_, v_i_6938_);
                    v_name_6952_ = lean_ctor_get(v_a_6951_, 0);
                    lean_inc(v_name_6952_);
                    v___x_6953_ = lean_mk_syntax_ident(v_name_6952_);
                    lean_inc(v___x_6953_);
                    v___x_6954_ =
                        l_Lean_resolveGlobalConst___at___00Lean_Elab_Tactic_evalSimpTrace_spec__1(
                            v___x_6953_,
                            v___y_6940_,
                            v___y_6941_,
                            v___y_6942_,
                            v___y_6943_,
                            v___y_6944_,
                            v___y_6945_,
                            v___y_6946_,
                            v___y_6947_,
                        );
                    if lean_obj_tag(v___x_6954_) == 0 {
                        v_a_6955_ = lean_ctor_get(v___x_6954_, 0);
                        lean_inc(v_a_6955_);
                        lean_dec_ref_known(v___x_6954_, 1);
                        v___x_6956_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(v___x_6953_, v_a_6955_, v_b_6939_, v___y_6946_);
                        lean_dec(v_a_6955_);
                        lean_dec(v___x_6953_);
                        if lean_obj_tag(v___x_6956_) == 0 {
                            v_a_6957_ = lean_ctor_get(v___x_6956_, 0);
                            lean_inc(v_a_6957_);
                            lean_dec_ref_known(v___x_6956_, 1);
                            v___x_6958_ = 1usize;
                            v___x_6959_ = lean_usize_add(v_i_6938_, v___x_6958_);
                            v_i_6938_ = v___x_6959_;
                            v_b_6939_ = v_a_6957_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_6956_;
                        }
                    } else {
                        lean_dec(v___x_6953_);
                        lean_dec_ref(v_b_6939_);
                        v_a_6961_ = lean_ctor_get(v___x_6954_, 0);
                        v_isSharedCheck_6968_ = (!lean_is_exclusive(v___x_6954_)) as u8;
                        if v_isSharedCheck_6968_ == 0 {
                            v___x_6963_ = v___x_6954_;
                            v_isShared_6964_ = v_isSharedCheck_6968_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6961_);
                            lean_dec(v___x_6954_);
                            v___x_6963_ = lean_box(0);
                            v_isShared_6964_ = v_isSharedCheck_6968_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6964_ == 0 {
                    v___x_6966_ = v___x_6963_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6967_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6967_, 0, v_a_6961_);
                    v___x_6966_ = v_reuseFailAlloc_6967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1___boxed(
    mut v_as_6969_: *mut LeanObject,
    mut v_sz_6970_: *mut LeanObject,
    mut v_i_6971_: *mut LeanObject,
    mut v_b_6972_: *mut LeanObject,
    mut v___y_6973_: *mut LeanObject,
    mut v___y_6974_: *mut LeanObject,
    mut v___y_6975_: *mut LeanObject,
    mut v___y_6976_: *mut LeanObject,
    mut v___y_6977_: *mut LeanObject,
    mut v___y_6978_: *mut LeanObject,
    mut v___y_6979_: *mut LeanObject,
    mut v___y_6980_: *mut LeanObject,
    mut v___y_6981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6982_: usize = 0;
    let mut v_i_boxed_6983_: usize = 0;
    let mut v_res_6984_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6982_ = lean_unbox_usize(v_sz_6970_);
    lean_dec(v_sz_6970_);
    v_i_boxed_6983_ = lean_unbox_usize(v_i_6971_);
    lean_dec(v_i_6971_);
    v_res_6984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_as_6969_, v_sz_boxed_6982_, v_i_boxed_6983_, v_b_6972_, v___y_6973_, v___y_6974_, v___y_6975_, v___y_6976_, v___y_6977_, v___y_6978_, v___y_6979_, v___y_6980_);
    lean_dec(v___y_6980_);
    lean_dec_ref(v___y_6979_);
    lean_dec(v___y_6978_);
    lean_dec_ref(v___y_6977_);
    lean_dec(v___y_6976_);
    lean_dec_ref(v___y_6975_);
    lean_dec(v___y_6974_);
    lean_dec_ref(v___y_6973_);
    lean_dec_ref(v_as_6969_);
    return v_res_6984_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0() -> *mut LeanObject {
    let mut v___x_6985_: *mut LeanObject = core::ptr::null_mut();
    v___x_6985_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6985_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1() -> *mut LeanObject {
    let mut v___x_6986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut LeanObject = core::ptr::null_mut();
    v___x_6986_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0_once),
        _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__0,
    );
    v___x_6987_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6987_, 0, v___x_6986_);
    return v___x_6987_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2() -> *mut LeanObject {
    let mut v___x_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut LeanObject = core::ptr::null_mut();
    v___x_6988_ = lean_unsigned_to_nat(0);
    v___x_6989_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once),
        _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1,
    );
    v___x_6990_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6990_, 0, v___x_6989_);
    lean_ctor_set(v___x_6990_, 1, v___x_6988_);
    return v___x_6990_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3() -> *mut LeanObject {
    let mut v___x_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut LeanObject = core::ptr::null_mut();
    v___x_6991_ = lean_unsigned_to_nat(32);
    v___x_6992_ = lean_mk_empty_array_with_capacity(v___x_6991_);
    v___x_6993_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6993_, 0, v___x_6992_);
    return v___x_6993_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4() -> *mut LeanObject {
    let mut v___x_6994_: usize = 0;
    let mut v___x_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut LeanObject = core::ptr::null_mut();
    v___x_6994_ = 5usize;
    v___x_6995_ = lean_unsigned_to_nat(0);
    v___x_6996_ = lean_unsigned_to_nat(32);
    v___x_6997_ = lean_mk_empty_array_with_capacity(v___x_6996_);
    v___x_6998_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3_once),
        _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__3,
    );
    v___x_6999_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_6999_, 0, v___x_6998_);
    lean_ctor_set(v___x_6999_, 1, v___x_6997_);
    lean_ctor_set(v___x_6999_, 2, v___x_6995_);
    lean_ctor_set(v___x_6999_, 3, v___x_6995_);
    lean_ctor_set_usize(v___x_6999_, 4, v___x_6994_);
    return v___x_6999_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5() -> *mut LeanObject {
    let mut v___x_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut LeanObject = core::ptr::null_mut();
    v___x_7000_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4_once),
        _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__4,
    );
    v___x_7001_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1_once),
        _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__1,
    );
    v___x_7002_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_7002_, 0, v___x_7001_);
    lean_ctor_set(v___x_7002_, 1, v___x_7001_);
    lean_ctor_set(v___x_7002_, 2, v___x_7001_);
    lean_ctor_set(v___x_7002_, 3, v___x_7000_);
    return v___x_7002_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6() -> *mut LeanObject {
    let mut v___x_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    v___x_7003_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5_once),
        _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__5,
    );
    v___x_7004_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2_once),
        _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__2,
    );
    v___x_7005_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7005_, 0, v___x_7004_);
    lean_ctor_set(v___x_7005_, 1, v___x_7003_);
    return v___x_7005_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(
    mut v___x_7014_: u8,
    mut v_stx_7015_: *mut LeanObject,
    mut v___x_7016_: u8,
    mut v___x_7017_: *mut LeanObject,
    mut v___x_7018_: *mut LeanObject,
    mut v___x_7019_: *mut LeanObject,
    mut v___f_7020_: *mut LeanObject,
    mut v___y_7021_: *mut LeanObject,
    mut v___y_7022_: *mut LeanObject,
    mut v___y_7023_: *mut LeanObject,
    mut v___y_7024_: *mut LeanObject,
    mut v___y_7025_: *mut LeanObject,
    mut v___y_7026_: *mut LeanObject,
    mut v___y_7027_: *mut LeanObject,
    mut v___y_7028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_7040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7044_: u8 = 0;
    let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: u8 = 0;
    let mut v___x_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7060_: u8 = 0;
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7064_: u8 = 0;
    let mut v_unused_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7069_: u8 = 0;
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7073_: u8 = 0;
    let mut v_reuseFailAlloc_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7078_: u8 = 0;
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7082_: u8 = 0;
    let mut v_isSharedCheck_7083_: u8 = 0;
    let mut v___y_7085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7105_: u8 = 0;
    let mut v___x_7107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7109_: u8 = 0;
    let mut v_snd_7110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7113_: u8 = 0;
    let mut v_val_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7122_: u8 = 0;
    let mut v___x_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7126_: u8 = 0;
    let mut v_reuseFailAlloc_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7128_: u8 = 0;
    let mut v_unused_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7133_: u8 = 0;
    let mut v___x_7135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7137_: u8 = 0;
    let mut v_a_7138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7141_: u8 = 0;
    let mut v___x_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7145_: u8 = 0;
    let mut v___y_7147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7148_: u8 = 0;
    let mut v___y_7149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7150_: u8 = 0;
    let mut v_stxForSuggestion_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocs_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocs_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocs_7168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7173_: u8 = 0;
    let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7177_: u8 = 0;
    let mut v___y_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7184_: u8 = 0;
    let mut v___y_7185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7197_: u8 = 0;
    let mut v___y_7198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7210_: u8 = 0;
    let mut v___y_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7222_: u8 = 0;
    let mut v___y_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7239_: u8 = 0;
    let mut v___y_7240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7251_: u8 = 0;
    let mut v___y_7252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7274_: u8 = 0;
    let mut v___y_7275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7286_: u8 = 0;
    let mut v___y_7287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7303_: u8 = 0;
    let mut v___y_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7314_: u8 = 0;
    let mut v___y_7315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7337_: u8 = 0;
    let mut v___y_7338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7349_: u8 = 0;
    let mut v___y_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7367_: u8 = 0;
    let mut v___y_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7379_: u8 = 0;
    let mut v___y_7380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7393_: u8 = 0;
    let mut v___y_7394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7404_: u8 = 0;
    let mut v___y_7405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7420_: u8 = 0;
    let mut v___y_7421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7429_: u8 = 0;
    let mut v___y_7430_: u8 = 0;
    let mut v_ref_7431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7444_: u8 = 0;
    let mut v___y_7445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7450_: u8 = 0;
    let mut v___y_7451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7460_: u8 = 0;
    let mut v___y_7461_: u8 = 0;
    let mut v_ref_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7492_: u8 = 0;
    let mut v___y_7493_: u8 = 0;
    let mut v_stxForExecution_7494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: u8 = 0;
    let mut v___x_7507_: u8 = 0;
    let mut v_ref_7508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: u8 = 0;
    let mut v___x_7510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7530_: u8 = 0;
    let mut v___y_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7542_: u8 = 0;
    let mut v___y_7543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7556_: u8 = 0;
    let mut v___y_7557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7568_: u8 = 0;
    let mut v___y_7569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7585_: u8 = 0;
    let mut v___y_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7599_: u8 = 0;
    let mut v___y_7600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7619_: u8 = 0;
    let mut v___y_7620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7633_: u8 = 0;
    let mut v___y_7634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7651_: u8 = 0;
    let mut v___y_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7664_: u8 = 0;
    let mut v___y_7665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7686_: u8 = 0;
    let mut v___y_7687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7698_: u8 = 0;
    let mut v___y_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7716_: u8 = 0;
    let mut v___y_7717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7729_: u8 = 0;
    let mut v___y_7730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7742_: u8 = 0;
    let mut v___y_7743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7755_: u8 = 0;
    let mut v___y_7756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7771_: u8 = 0;
    let mut v___y_7772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7780_: u8 = 0;
    let mut v___y_7781_: u8 = 0;
    let mut v_ref_7782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7800_: u8 = 0;
    let mut v___y_7801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7804_: u8 = 0;
    let mut v___y_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7810_: u8 = 0;
    let mut v___y_7811_: u8 = 0;
    let mut v_ref_7812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7841_: u8 = 0;
    let mut v___y_7842_: u8 = 0;
    let mut v_argsArray_7843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7853_: u8 = 0;
    let mut v___x_7854_: u8 = 0;
    let mut v_ref_7855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7856_: u8 = 0;
    let mut v___x_7857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7872_: u8 = 0;
    let mut v___y_7873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7883_: u8 = 0;
    let mut v___y_7884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7889_: usize = 0;
    let mut v___x_7890_: usize = 0;
    let mut v___x_7891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7896_: u8 = 0;
    let mut v___x_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7900_: u8 = 0;
    let mut v_a_7901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7904_: u8 = 0;
    let mut v___x_7906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7908_: u8 = 0;
    let mut v_a_7909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7912_: u8 = 0;
    let mut v___x_7914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7916_: u8 = 0;
    let mut v___y_7918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7921_: u8 = 0;
    let mut v___y_7922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7932_: u8 = 0;
    let mut v___y_7933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_7934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suggestions_7935_: u8 = 0;
    let mut v_maxSuggestions_7936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7956_: u8 = 0;
    let mut v___y_7957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: u8 = 0;
    let mut v___x_7959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7968_: u8 = 0;
    let mut v___x_7970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7972_: u8 = 0;
    let mut v___y_7974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7978_: u8 = 0;
    let mut v_args_7979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7993_: u8 = 0;
    let mut v___x_7995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7997_: u8 = 0;
    let mut v___x_7998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8004_: u8 = 0;
    let mut v_o_8005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: u8 = 0;
    let mut v___x_8017_: u8 = 0;
    let mut v___x_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8022_: u8 = 0;
    let mut v___x_8023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_8025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bang_8029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8042_: u8 = 0;
    let mut v___x_8043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cfg_8044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8047_: u8 = 0;
    let mut v___x_8048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8051_: u8 = 0;
    let mut v___x_8052_: u8 = 0;
    let mut v___x_8053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_o_8054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8058_: u8 = 0;
    let mut v___x_8059_: u8 = 0;
    let mut v___x_8060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bang_8061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8063_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_7014_ == 0 {
                    lean_dec_ref(v___f_7020_);
                    lean_dec_ref(v___x_7019_);
                    lean_dec_ref(v___x_7018_);
                    lean_dec_ref(v___x_7017_);
                    v___x_7030_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                    return v___x_7030_;
                } else {
                    v___x_7031_ = lean_unsigned_to_nat(0);
                    v_tk_7032_ = l_Lean_Syntax_getArg(v_stx_7015_, v___x_7031_);
                    v___x_7998_ = lean_unsigned_to_nat(1);
                    v___x_8057_ = l_Lean_Syntax_getArg(v_stx_7015_, v___x_7998_);
                    v___x_8058_ = l_Lean_Syntax_isNone(v___x_8057_);
                    if v___x_8058_ == 0 {
                        lean_inc(v___x_8057_);
                        v___x_8059_ = l_Lean_Syntax_matchesNull(v___x_8057_, v___x_7998_);
                        if v___x_8059_ == 0 {
                            lean_dec(v___x_8057_);
                            lean_dec(v_tk_7032_);
                            lean_dec_ref(v___f_7020_);
                            lean_dec_ref(v___x_7019_);
                            lean_dec_ref(v___x_7018_);
                            lean_dec_ref(v___x_7017_);
                            v___x_8060_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                            return v___x_8060_;
                        } else {
                            v_bang_8061_ = l_Lean_Syntax_getArg(v___x_8057_, v___x_7031_);
                            lean_dec(v___x_8057_);
                            v___x_8062_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_8062_, 0, v_bang_8061_);
                            v_bang_8029_ = v___x_8062_;
                            v___y_8030_ = v___y_7021_;
                            v___y_8031_ = v___y_7022_;
                            v___y_8032_ = v___y_7023_;
                            v___y_8033_ = v___y_7024_;
                            v___y_8034_ = v___y_7025_;
                            v___y_8035_ = v___y_7026_;
                            v___y_8036_ = v___y_7027_;
                            v___y_8037_ = v___y_7028_;
                            state = 61;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_8057_);
                        v___x_8063_ = lean_box(0);
                        v_bang_8029_ = v___x_8063_;
                        v___y_8030_ = v___y_7021_;
                        v___y_8031_ = v___y_7022_;
                        v___y_8032_ = v___y_7023_;
                        v___y_8033_ = v___y_7024_;
                        v___y_8034_ = v___y_7025_;
                        v___y_8035_ = v___y_7026_;
                        v___y_8036_ = v___y_7027_;
                        v___y_8037_ = v___y_7028_;
                        state = 61;
                        continue;
                    }
                }
            }
            1 => {
                v_usedTheorems_7040_ = lean_ctor_get(v___y_7035_, 0);
                v_diag_7041_ = lean_ctor_get(v___y_7035_, 1);
                v_isSharedCheck_7083_ = (!lean_is_exclusive(v___y_7035_)) as u8;
                if v_isSharedCheck_7083_ == 0 {
                    v___x_7043_ = v___y_7035_;
                    v_isShared_7044_ = v_isSharedCheck_7083_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_diag_7041_);
                    lean_inc(v_usedTheorems_7040_);
                    lean_dec(v___y_7035_);
                    v___x_7043_ = lean_box(0);
                    v_isShared_7044_ = v_isSharedCheck_7083_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7045_ = l_Lean_Elab_Tactic_mkSimpCallStx(
                    v___y_7034_,
                    v_usedTheorems_7040_,
                    v___y_7036_,
                    v___y_7037_,
                    v___y_7038_,
                    v___y_7039_,
                );
                lean_dec_ref(v_usedTheorems_7040_);
                if lean_obj_tag(v___x_7045_) == 0 {
                    v_a_7046_ = lean_ctor_get(v___x_7045_, 0);
                    lean_inc(v_a_7046_);
                    lean_dec_ref_known(v___x_7045_, 1);
                    v_ref_7047_ = lean_ctor_get(v___y_7038_, 5);
                    v___x_7048_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
                    if v_isShared_7044_ == 0 {
                        lean_ctor_set(v___x_7043_, 1, v_a_7046_);
                        lean_ctor_set(v___x_7043_, 0, v___x_7048_);
                        v___x_7050_ = v___x_7043_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7074_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7074_, 0, v___x_7048_);
                        lean_ctor_set(v_reuseFailAlloc_7074_, 1, v_a_7046_);
                        v___x_7050_ = v_reuseFailAlloc_7074_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7043_);
                    lean_dec_ref(v_diag_7041_);
                    lean_dec(v_tk_7032_);
                    v_a_7075_ = lean_ctor_get(v___x_7045_, 0);
                    v_isSharedCheck_7082_ = (!lean_is_exclusive(v___x_7045_)) as u8;
                    if v_isSharedCheck_7082_ == 0 {
                        v___x_7077_ = v___x_7045_;
                        v_isShared_7078_ = v_isSharedCheck_7082_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_7075_);
                        lean_dec(v___x_7045_);
                        v___x_7077_ = lean_box(0);
                        v_isShared_7078_ = v_isSharedCheck_7082_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7051_ = lean_box(0);
                v___x_7052_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_7052_, 0, v___x_7050_);
                lean_ctor_set(v___x_7052_, 1, v___x_7051_);
                lean_ctor_set(v___x_7052_, 2, v___x_7051_);
                lean_ctor_set(v___x_7052_, 3, v___x_7051_);
                lean_ctor_set(v___x_7052_, 4, v___x_7051_);
                lean_ctor_set(v___x_7052_, 5, v___x_7051_);
                lean_inc(v_ref_7047_);
                v___x_7053_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7053_, 0, v_ref_7047_);
                v___x_7054_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
                v___x_7055_ = 4;
                v___x_7056_ = l_Lean_MessageData_nil;
                v___x_7057_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_tk_7032_,
                    v___x_7052_,
                    v___x_7053_,
                    v___x_7054_,
                    v___x_7051_,
                    v___x_7055_,
                    v___x_7056_,
                    v___y_7038_,
                    v___y_7039_,
                );
                if lean_obj_tag(v___x_7057_) == 0 {
                    v_isSharedCheck_7064_ = (!lean_is_exclusive(v___x_7057_)) as u8;
                    if v_isSharedCheck_7064_ == 0 {
                        v_unused_7065_ = lean_ctor_get(v___x_7057_, 0);
                        lean_dec(v_unused_7065_);
                        v___x_7059_ = v___x_7057_;
                        v_isShared_7060_ = v_isSharedCheck_7064_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_7057_);
                        v___x_7059_ = lean_box(0);
                        v_isShared_7060_ = v_isSharedCheck_7064_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_diag_7041_);
                    v_a_7066_ = lean_ctor_get(v___x_7057_, 0);
                    v_isSharedCheck_7073_ = (!lean_is_exclusive(v___x_7057_)) as u8;
                    if v_isSharedCheck_7073_ == 0 {
                        v___x_7068_ = v___x_7057_;
                        v_isShared_7069_ = v_isSharedCheck_7073_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_7066_);
                        lean_dec(v___x_7057_);
                        v___x_7068_ = lean_box(0);
                        v_isShared_7069_ = v_isSharedCheck_7073_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_7060_ == 0 {
                    lean_ctor_set(v___x_7059_, 0, v_diag_7041_);
                    v___x_7062_ = v___x_7059_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7063_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7063_, 0, v_diag_7041_);
                    v___x_7062_ = v_reuseFailAlloc_7063_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7062_;
            }
            6 => {
                if v_isShared_7069_ == 0 {
                    v___x_7071_ = v___x_7068_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7072_, 0, v_a_7066_);
                    v___x_7071_ = v_reuseFailAlloc_7072_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7071_;
            }
            8 => {
                if v_isShared_7078_ == 0 {
                    v___x_7080_ = v___x_7077_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7081_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7081_, 0, v_a_7075_);
                    v___x_7080_ = v_reuseFailAlloc_7081_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7080_;
            }
            10 => {
                v___x_7093_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_7090_,
                    v___y_7089_,
                    v___y_7088_,
                    v___y_7086_,
                    v___y_7091_,
                );
                if lean_obj_tag(v___x_7093_) == 0 {
                    v_a_7094_ = lean_ctor_get(v___x_7093_, 0);
                    lean_inc(v_a_7094_);
                    lean_dec_ref_known(v___x_7093_, 1);
                    v___x_7095_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once
                        ),
                        _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6,
                    );
                    v___x_7096_ = l_Lean_Meta_simpAll(
                        v_a_7094_,
                        v___y_7092_,
                        v___y_7085_,
                        v___x_7095_,
                        v___y_7089_,
                        v___y_7088_,
                        v___y_7086_,
                        v___y_7091_,
                    );
                    if lean_obj_tag(v___x_7096_) == 0 {
                        v_a_7097_ = lean_ctor_get(v___x_7096_, 0);
                        lean_inc(v_a_7097_);
                        lean_dec_ref_known(v___x_7096_, 1);
                        v_fst_7098_ = lean_ctor_get(v_a_7097_, 0);
                        if lean_obj_tag(v_fst_7098_) == 0 {
                            v_snd_7099_ = lean_ctor_get(v_a_7097_, 1);
                            lean_inc(v_snd_7099_);
                            lean_dec(v_a_7097_);
                            v___x_7100_ = lean_box(0);
                            v___x_7101_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v___x_7100_,
                                v___y_7090_,
                                v___y_7089_,
                                v___y_7088_,
                                v___y_7086_,
                                v___y_7091_,
                            );
                            if lean_obj_tag(v___x_7101_) == 0 {
                                lean_dec_ref_known(v___x_7101_, 1);
                                v___y_7034_ = v___y_7087_;
                                v___y_7035_ = v_snd_7099_;
                                v___y_7036_ = v___y_7089_;
                                v___y_7037_ = v___y_7088_;
                                v___y_7038_ = v___y_7086_;
                                v___y_7039_ = v___y_7091_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_snd_7099_);
                                lean_dec(v___y_7087_);
                                lean_dec(v_tk_7032_);
                                v_a_7102_ = lean_ctor_get(v___x_7101_, 0);
                                v_isSharedCheck_7109_ = (!lean_is_exclusive(v___x_7101_)) as u8;
                                if v_isSharedCheck_7109_ == 0 {
                                    v___x_7104_ = v___x_7101_;
                                    v_isShared_7105_ = v_isSharedCheck_7109_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_7102_);
                                    lean_dec(v___x_7101_);
                                    v___x_7104_ = lean_box(0);
                                    v_isShared_7105_ = v_isSharedCheck_7109_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc_ref(v_fst_7098_);
                            v_snd_7110_ = lean_ctor_get(v_a_7097_, 1);
                            v_isSharedCheck_7128_ = (!lean_is_exclusive(v_a_7097_)) as u8;
                            if v_isSharedCheck_7128_ == 0 {
                                v_unused_7129_ = lean_ctor_get(v_a_7097_, 0);
                                lean_dec(v_unused_7129_);
                                v___x_7112_ = v_a_7097_;
                                v_isShared_7113_ = v_isSharedCheck_7128_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_snd_7110_);
                                lean_dec(v_a_7097_);
                                v___x_7112_ = lean_box(0);
                                v_isShared_7113_ = v_isSharedCheck_7128_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_7087_);
                        lean_dec(v_tk_7032_);
                        v_a_7130_ = lean_ctor_get(v___x_7096_, 0);
                        v_isSharedCheck_7137_ = (!lean_is_exclusive(v___x_7096_)) as u8;
                        if v_isSharedCheck_7137_ == 0 {
                            v___x_7132_ = v___x_7096_;
                            v_isShared_7133_ = v_isSharedCheck_7137_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_7130_);
                            lean_dec(v___x_7096_);
                            v___x_7132_ = lean_box(0);
                            v_isShared_7133_ = v_isSharedCheck_7137_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7092_);
                    lean_dec(v___y_7087_);
                    lean_dec_ref(v___y_7085_);
                    lean_dec(v_tk_7032_);
                    v_a_7138_ = lean_ctor_get(v___x_7093_, 0);
                    v_isSharedCheck_7145_ = (!lean_is_exclusive(v___x_7093_)) as u8;
                    if v_isSharedCheck_7145_ == 0 {
                        v___x_7140_ = v___x_7093_;
                        v_isShared_7141_ = v_isSharedCheck_7145_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_7138_);
                        lean_dec(v___x_7093_);
                        v___x_7140_ = lean_box(0);
                        v_isShared_7141_ = v_isSharedCheck_7145_;
                        state = 19;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_7105_ == 0 {
                    v___x_7107_ = v___x_7104_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7108_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7108_, 0, v_a_7102_);
                    v___x_7107_ = v_reuseFailAlloc_7108_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7107_;
            }
            13 => {
                v_val_7114_ = lean_ctor_get(v_fst_7098_, 0);
                lean_inc(v_val_7114_);
                lean_dec_ref_known(v_fst_7098_, 1);
                v___x_7115_ = lean_box(0);
                if v_isShared_7113_ == 0 {
                    lean_ctor_set_tag(v___x_7112_, 1);
                    lean_ctor_set(v___x_7112_, 1, v___x_7115_);
                    lean_ctor_set(v___x_7112_, 0, v_val_7114_);
                    v___x_7117_ = v___x_7112_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7127_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7127_, 0, v_val_7114_);
                    lean_ctor_set(v_reuseFailAlloc_7127_, 1, v___x_7115_);
                    v___x_7117_ = v_reuseFailAlloc_7127_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_7118_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_7117_,
                    v___y_7090_,
                    v___y_7089_,
                    v___y_7088_,
                    v___y_7086_,
                    v___y_7091_,
                );
                if lean_obj_tag(v___x_7118_) == 0 {
                    lean_dec_ref_known(v___x_7118_, 1);
                    v___y_7034_ = v___y_7087_;
                    v___y_7035_ = v_snd_7110_;
                    v___y_7036_ = v___y_7089_;
                    v___y_7037_ = v___y_7088_;
                    v___y_7038_ = v___y_7086_;
                    v___y_7039_ = v___y_7091_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_snd_7110_);
                    lean_dec(v___y_7087_);
                    lean_dec(v_tk_7032_);
                    v_a_7119_ = lean_ctor_get(v___x_7118_, 0);
                    v_isSharedCheck_7126_ = (!lean_is_exclusive(v___x_7118_)) as u8;
                    if v_isSharedCheck_7126_ == 0 {
                        v___x_7121_ = v___x_7118_;
                        v_isShared_7122_ = v_isSharedCheck_7126_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_7119_);
                        lean_dec(v___x_7118_);
                        v___x_7121_ = lean_box(0);
                        v_isShared_7122_ = v_isSharedCheck_7126_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_7122_ == 0 {
                    v___x_7124_ = v___x_7121_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7125_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7125_, 0, v_a_7119_);
                    v___x_7124_ = v_reuseFailAlloc_7125_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7124_;
            }
            17 => {
                if v_isShared_7133_ == 0 {
                    v___x_7135_ = v___x_7132_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7136_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7136_, 0, v_a_7130_);
                    v___x_7135_ = v_reuseFailAlloc_7136_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7135_;
            }
            19 => {
                if v_isShared_7141_ == 0 {
                    v___x_7143_ = v___x_7140_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7144_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7144_, 0, v_a_7138_);
                    v___x_7143_ = v_reuseFailAlloc_7144_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_7143_;
            }
            21 => {
                v___x_7160_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3;
                v___x_7161_ = l_Lean_Elab_Tactic_mkSimpContext(
                    v___y_7149_,
                    v___x_7016_,
                    v___y_7148_,
                    v___x_7016_,
                    v___x_7160_,
                    v___y_7152_,
                    v___y_7153_,
                    v___y_7154_,
                    v___y_7155_,
                    v___y_7156_,
                    v___y_7157_,
                    v___y_7158_,
                    v___y_7159_,
                );
                lean_dec(v___y_7149_);
                if lean_obj_tag(v___x_7161_) == 0 {
                    v_a_7162_ = lean_ctor_get(v___x_7161_, 0);
                    lean_inc(v_a_7162_);
                    lean_dec_ref_known(v___x_7161_, 1);
                    if lean_obj_tag(v___y_7147_) == 0 {
                        v_ctx_7163_ = lean_ctor_get(v_a_7162_, 0);
                        lean_inc_ref(v_ctx_7163_);
                        v_simprocs_7164_ = lean_ctor_get(v_a_7162_, 1);
                        lean_inc_ref(v_simprocs_7164_);
                        lean_dec(v_a_7162_);
                        v___y_7085_ = v_simprocs_7164_;
                        v___y_7086_ = v___y_7158_;
                        v___y_7087_ = v_stxForSuggestion_7151_;
                        v___y_7088_ = v___y_7157_;
                        v___y_7089_ = v___y_7156_;
                        v___y_7090_ = v___y_7153_;
                        v___y_7091_ = v___y_7159_;
                        v___y_7092_ = v_ctx_7163_;
                        state = 10;
                        continue;
                    } else {
                        lean_dec_ref_known(v___y_7147_, 1);
                        if v___y_7150_ == 0 {
                            v_ctx_7165_ = lean_ctor_get(v_a_7162_, 0);
                            lean_inc_ref(v_ctx_7165_);
                            v_simprocs_7166_ = lean_ctor_get(v_a_7162_, 1);
                            lean_inc_ref(v_simprocs_7166_);
                            lean_dec(v_a_7162_);
                            v___y_7085_ = v_simprocs_7166_;
                            v___y_7086_ = v___y_7158_;
                            v___y_7087_ = v_stxForSuggestion_7151_;
                            v___y_7088_ = v___y_7157_;
                            v___y_7089_ = v___y_7156_;
                            v___y_7090_ = v___y_7153_;
                            v___y_7091_ = v___y_7159_;
                            v___y_7092_ = v_ctx_7165_;
                            state = 10;
                            continue;
                        } else {
                            v_ctx_7167_ = lean_ctor_get(v_a_7162_, 0);
                            lean_inc_ref(v_ctx_7167_);
                            v_simprocs_7168_ = lean_ctor_get(v_a_7162_, 1);
                            lean_inc_ref(v_simprocs_7168_);
                            lean_dec(v_a_7162_);
                            v___x_7169_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_7167_);
                            v___y_7085_ = v_simprocs_7168_;
                            v___y_7086_ = v___y_7158_;
                            v___y_7087_ = v_stxForSuggestion_7151_;
                            v___y_7088_ = v___y_7157_;
                            v___y_7089_ = v___y_7156_;
                            v___y_7090_ = v___y_7153_;
                            v___y_7091_ = v___y_7159_;
                            v___y_7092_ = v___x_7169_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_stxForSuggestion_7151_);
                    lean_dec(v___y_7147_);
                    lean_dec(v_tk_7032_);
                    v_a_7170_ = lean_ctor_get(v___x_7161_, 0);
                    v_isSharedCheck_7177_ = (!lean_is_exclusive(v___x_7161_)) as u8;
                    if v_isSharedCheck_7177_ == 0 {
                        v___x_7172_ = v___x_7161_;
                        v_isShared_7173_ = v_isSharedCheck_7177_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_7170_);
                        lean_dec(v___x_7161_);
                        v___x_7172_ = lean_box(0);
                        v_isShared_7173_ = v_isSharedCheck_7177_;
                        state = 22;
                        continue;
                    }
                }
            }
            22 => {
                if v_isShared_7173_ == 0 {
                    v___x_7175_ = v___x_7172_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7176_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7176_, 0, v_a_7170_);
                    v___x_7175_ = v_reuseFailAlloc_7176_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_7175_;
            }
            24 => {
                lean_inc_ref_n(v___y_7186_, 2);
                v___x_7199_ = l_Array_append___redArg(v___y_7186_, v___y_7198_);
                lean_dec_ref(v___y_7198_);
                lean_inc_n(v___y_7189_, 2);
                lean_inc_n(v___y_7181_, 2);
                v___x_7200_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7200_, 0, v___y_7181_);
                lean_ctor_set(v___x_7200_, 1, v___y_7189_);
                lean_ctor_set(v___x_7200_, 2, v___x_7199_);
                v___x_7201_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7201_, 0, v___y_7181_);
                lean_ctor_set(v___x_7201_, 1, v___y_7189_);
                lean_ctor_set(v___x_7201_, 2, v___y_7186_);
                v___x_7202_ = l_Lean_Syntax_node5(
                    v___y_7181_,
                    v___y_7196_,
                    v___y_7190_,
                    v___y_7187_,
                    v___y_7192_,
                    v___x_7200_,
                    v___x_7201_,
                );
                v___y_7147_ = v___y_7194_;
                v___y_7148_ = v___y_7184_;
                v___y_7149_ = v___y_7195_;
                v___y_7150_ = v___y_7197_;
                v_stxForSuggestion_7151_ = v___x_7202_;
                v___y_7152_ = v___y_7193_;
                v___y_7153_ = v___y_7182_;
                v___y_7154_ = v___y_7183_;
                v___y_7155_ = v___y_7179_;
                v___y_7156_ = v___y_7180_;
                v___y_7157_ = v___y_7188_;
                v___y_7158_ = v___y_7191_;
                v___y_7159_ = v___y_7185_;
                state = 21;
                continue;
            }
            25 => {
                lean_inc_ref(v___y_7212_);
                v___x_7224_ = l_Array_append___redArg(v___y_7212_, v___y_7223_);
                lean_dec_ref(v___y_7223_);
                lean_inc(v___y_7215_);
                lean_inc(v___y_7207_);
                v___x_7225_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7225_, 0, v___y_7207_);
                lean_ctor_set(v___x_7225_, 1, v___y_7215_);
                lean_ctor_set(v___x_7225_, 2, v___x_7224_);
                if lean_obj_tag(v___y_7206_) == 1 {
                    v_val_7226_ = lean_ctor_get(v___y_7206_, 0);
                    lean_inc(v_val_7226_);
                    lean_dec_ref_known(v___y_7206_, 1);
                    v___x_7227_ = l_Lean_SourceInfo_fromRef(v_val_7226_, v___x_7016_);
                    lean_dec(v_val_7226_);
                    v___x_7228_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_7229_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_7229_, 0, v___x_7227_);
                    lean_ctor_set(v___x_7229_, 1, v___x_7228_);
                    v___x_7230_ = l_Array_mkArray1___redArg(v___x_7229_);
                    v___y_7179_ = v___y_7204_;
                    v___y_7180_ = v___y_7205_;
                    v___y_7181_ = v___y_7207_;
                    v___y_7182_ = v___y_7208_;
                    v___y_7183_ = v___y_7209_;
                    v___y_7184_ = v___y_7210_;
                    v___y_7185_ = v___y_7211_;
                    v___y_7186_ = v___y_7212_;
                    v___y_7187_ = v___y_7213_;
                    v___y_7188_ = v___y_7214_;
                    v___y_7189_ = v___y_7215_;
                    v___y_7190_ = v___y_7216_;
                    v___y_7191_ = v___y_7217_;
                    v___y_7192_ = v___x_7225_;
                    v___y_7193_ = v___y_7218_;
                    v___y_7194_ = v___y_7219_;
                    v___y_7195_ = v___y_7221_;
                    v___y_7196_ = v___y_7220_;
                    v___y_7197_ = v___y_7222_;
                    v___y_7198_ = v___x_7230_;
                    state = 24;
                    continue;
                } else {
                    lean_dec(v___y_7206_);
                    v___x_7231_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_7179_ = v___y_7204_;
                    v___y_7180_ = v___y_7205_;
                    v___y_7181_ = v___y_7207_;
                    v___y_7182_ = v___y_7208_;
                    v___y_7183_ = v___y_7209_;
                    v___y_7184_ = v___y_7210_;
                    v___y_7185_ = v___y_7211_;
                    v___y_7186_ = v___y_7212_;
                    v___y_7187_ = v___y_7213_;
                    v___y_7188_ = v___y_7214_;
                    v___y_7189_ = v___y_7215_;
                    v___y_7190_ = v___y_7216_;
                    v___y_7191_ = v___y_7217_;
                    v___y_7192_ = v___x_7225_;
                    v___y_7193_ = v___y_7218_;
                    v___y_7194_ = v___y_7219_;
                    v___y_7195_ = v___y_7221_;
                    v___y_7196_ = v___y_7220_;
                    v___y_7197_ = v___y_7222_;
                    v___y_7198_ = v___x_7231_;
                    state = 24;
                    continue;
                }
            }
            26 => {
                lean_inc_ref_n(v___y_7236_, 2);
                v___x_7254_ = l_Array_append___redArg(v___y_7236_, v___y_7253_);
                lean_dec_ref(v___y_7253_);
                lean_inc_n(v___y_7233_, 3);
                lean_inc_n(v___y_7247_, 5);
                v___x_7255_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7255_, 0, v___y_7247_);
                lean_ctor_set(v___x_7255_, 1, v___y_7233_);
                lean_ctor_set(v___x_7255_, 2, v___x_7254_);
                v___x_7256_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
                v___x_7257_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7257_, 0, v___y_7247_);
                lean_ctor_set(v___x_7257_, 1, v___x_7256_);
                v___x_7258_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
                v___x_7259_ = l_Lean_Syntax_SepArray_ofElems(v___x_7258_, v___y_7240_);
                lean_dec_ref(v___y_7240_);
                v___x_7260_ = l_Array_append___redArg(v___y_7236_, v___x_7259_);
                lean_dec_ref(v___x_7259_);
                v___x_7261_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7261_, 0, v___y_7247_);
                lean_ctor_set(v___x_7261_, 1, v___y_7233_);
                lean_ctor_set(v___x_7261_, 2, v___x_7260_);
                v___x_7262_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
                v___x_7263_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7263_, 0, v___y_7247_);
                lean_ctor_set(v___x_7263_, 1, v___x_7262_);
                v___x_7264_ = l_Lean_Syntax_node3(
                    v___y_7247_,
                    v___y_7233_,
                    v___x_7257_,
                    v___x_7261_,
                    v___x_7263_,
                );
                v___x_7265_ = l_Lean_Syntax_node5(
                    v___y_7247_,
                    v___y_7242_,
                    v___y_7252_,
                    v___y_7243_,
                    v___y_7249_,
                    v___x_7255_,
                    v___x_7264_,
                );
                v___y_7147_ = v___y_7248_;
                v___y_7148_ = v___y_7239_;
                v___y_7149_ = v___y_7250_;
                v___y_7150_ = v___y_7251_;
                v_stxForSuggestion_7151_ = v___x_7265_;
                v___y_7152_ = v___y_7246_;
                v___y_7153_ = v___y_7237_;
                v___y_7154_ = v___y_7238_;
                v___y_7155_ = v___y_7234_;
                v___y_7156_ = v___y_7235_;
                v___y_7157_ = v___y_7244_;
                v___y_7158_ = v___y_7245_;
                v___y_7159_ = v___y_7241_;
                state = 21;
                continue;
            }
            27 => {
                lean_inc_ref(v___y_7271_);
                v___x_7288_ = l_Array_append___redArg(v___y_7271_, v___y_7287_);
                lean_dec_ref(v___y_7287_);
                lean_inc(v___y_7267_);
                lean_inc(v___y_7282_);
                v___x_7289_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7289_, 0, v___y_7282_);
                lean_ctor_set(v___x_7289_, 1, v___y_7267_);
                lean_ctor_set(v___x_7289_, 2, v___x_7288_);
                if lean_obj_tag(v___y_7270_) == 1 {
                    v_val_7290_ = lean_ctor_get(v___y_7270_, 0);
                    lean_inc(v_val_7290_);
                    lean_dec_ref_known(v___y_7270_, 1);
                    v___x_7291_ = l_Lean_SourceInfo_fromRef(v_val_7290_, v___x_7016_);
                    lean_dec(v_val_7290_);
                    v___x_7292_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_7293_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_7293_, 0, v___x_7291_);
                    lean_ctor_set(v___x_7293_, 1, v___x_7292_);
                    v___x_7294_ = l_Array_mkArray1___redArg(v___x_7293_);
                    v___y_7233_ = v___y_7267_;
                    v___y_7234_ = v___y_7268_;
                    v___y_7235_ = v___y_7269_;
                    v___y_7236_ = v___y_7271_;
                    v___y_7237_ = v___y_7272_;
                    v___y_7238_ = v___y_7273_;
                    v___y_7239_ = v___y_7274_;
                    v___y_7240_ = v___y_7275_;
                    v___y_7241_ = v___y_7276_;
                    v___y_7242_ = v___y_7277_;
                    v___y_7243_ = v___y_7278_;
                    v___y_7244_ = v___y_7279_;
                    v___y_7245_ = v___y_7280_;
                    v___y_7246_ = v___y_7281_;
                    v___y_7247_ = v___y_7282_;
                    v___y_7248_ = v___y_7283_;
                    v___y_7249_ = v___x_7289_;
                    v___y_7250_ = v___y_7284_;
                    v___y_7251_ = v___y_7286_;
                    v___y_7252_ = v___y_7285_;
                    v___y_7253_ = v___x_7294_;
                    state = 26;
                    continue;
                } else {
                    lean_dec(v___y_7270_);
                    v___x_7295_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_7233_ = v___y_7267_;
                    v___y_7234_ = v___y_7268_;
                    v___y_7235_ = v___y_7269_;
                    v___y_7236_ = v___y_7271_;
                    v___y_7237_ = v___y_7272_;
                    v___y_7238_ = v___y_7273_;
                    v___y_7239_ = v___y_7274_;
                    v___y_7240_ = v___y_7275_;
                    v___y_7241_ = v___y_7276_;
                    v___y_7242_ = v___y_7277_;
                    v___y_7243_ = v___y_7278_;
                    v___y_7244_ = v___y_7279_;
                    v___y_7245_ = v___y_7280_;
                    v___y_7246_ = v___y_7281_;
                    v___y_7247_ = v___y_7282_;
                    v___y_7248_ = v___y_7283_;
                    v___y_7249_ = v___x_7289_;
                    v___y_7250_ = v___y_7284_;
                    v___y_7251_ = v___y_7286_;
                    v___y_7252_ = v___y_7285_;
                    v___y_7253_ = v___x_7295_;
                    state = 26;
                    continue;
                }
            }
            28 => {
                lean_inc_ref_n(v___y_7308_, 2);
                v___x_7318_ = l_Array_append___redArg(v___y_7308_, v___y_7317_);
                lean_dec_ref(v___y_7317_);
                lean_inc_n(v___y_7315_, 3);
                lean_inc_n(v___y_7298_, 5);
                v___x_7319_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7319_, 0, v___y_7298_);
                lean_ctor_set(v___x_7319_, 1, v___y_7315_);
                lean_ctor_set(v___x_7319_, 2, v___x_7318_);
                v___x_7320_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
                v___x_7321_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7321_, 0, v___y_7298_);
                lean_ctor_set(v___x_7321_, 1, v___x_7320_);
                v___x_7322_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
                v___x_7323_ = l_Lean_Syntax_SepArray_ofElems(v___x_7322_, v___y_7304_);
                lean_dec_ref(v___y_7304_);
                v___x_7324_ = l_Array_append___redArg(v___y_7308_, v___x_7323_);
                lean_dec_ref(v___x_7323_);
                v___x_7325_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7325_, 0, v___y_7298_);
                lean_ctor_set(v___x_7325_, 1, v___y_7315_);
                lean_ctor_set(v___x_7325_, 2, v___x_7324_);
                v___x_7326_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
                v___x_7327_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7327_, 0, v___y_7298_);
                lean_ctor_set(v___x_7327_, 1, v___x_7326_);
                v___x_7328_ = l_Lean_Syntax_node3(
                    v___y_7298_,
                    v___y_7315_,
                    v___x_7321_,
                    v___x_7325_,
                    v___x_7327_,
                );
                v___x_7329_ = l_Lean_Syntax_node5(
                    v___y_7298_,
                    v___y_7316_,
                    v___y_7310_,
                    v___y_7306_,
                    v___y_7300_,
                    v___x_7319_,
                    v___x_7328_,
                );
                v___y_7147_ = v___y_7312_;
                v___y_7148_ = v___y_7303_;
                v___y_7149_ = v___y_7313_;
                v___y_7150_ = v___y_7314_;
                v_stxForSuggestion_7151_ = v___x_7329_;
                v___y_7152_ = v___y_7311_;
                v___y_7153_ = v___y_7301_;
                v___y_7154_ = v___y_7302_;
                v___y_7155_ = v___y_7297_;
                v___y_7156_ = v___y_7299_;
                v___y_7157_ = v___y_7307_;
                v___y_7158_ = v___y_7309_;
                v___y_7159_ = v___y_7305_;
                state = 21;
                continue;
            }
            29 => {
                lean_inc_ref(v___y_7342_);
                v___x_7352_ = l_Array_append___redArg(v___y_7342_, v___y_7351_);
                lean_dec_ref(v___y_7351_);
                lean_inc(v___y_7350_);
                lean_inc(v___y_7332_);
                v___x_7353_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7353_, 0, v___y_7332_);
                lean_ctor_set(v___x_7353_, 1, v___y_7350_);
                lean_ctor_set(v___x_7353_, 2, v___x_7352_);
                if lean_obj_tag(v___y_7334_) == 1 {
                    v_val_7354_ = lean_ctor_get(v___y_7334_, 0);
                    lean_inc(v_val_7354_);
                    lean_dec_ref_known(v___y_7334_, 1);
                    v___x_7355_ = l_Lean_SourceInfo_fromRef(v_val_7354_, v___x_7016_);
                    lean_dec(v_val_7354_);
                    v___x_7356_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_7357_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_7357_, 0, v___x_7355_);
                    lean_ctor_set(v___x_7357_, 1, v___x_7356_);
                    v___x_7358_ = l_Array_mkArray1___redArg(v___x_7357_);
                    v___y_7297_ = v___y_7331_;
                    v___y_7298_ = v___y_7332_;
                    v___y_7299_ = v___y_7333_;
                    v___y_7300_ = v___x_7353_;
                    v___y_7301_ = v___y_7335_;
                    v___y_7302_ = v___y_7336_;
                    v___y_7303_ = v___y_7337_;
                    v___y_7304_ = v___y_7338_;
                    v___y_7305_ = v___y_7339_;
                    v___y_7306_ = v___y_7340_;
                    v___y_7307_ = v___y_7341_;
                    v___y_7308_ = v___y_7342_;
                    v___y_7309_ = v___y_7344_;
                    v___y_7310_ = v___y_7343_;
                    v___y_7311_ = v___y_7345_;
                    v___y_7312_ = v___y_7346_;
                    v___y_7313_ = v___y_7347_;
                    v___y_7314_ = v___y_7349_;
                    v___y_7315_ = v___y_7350_;
                    v___y_7316_ = v___y_7348_;
                    v___y_7317_ = v___x_7358_;
                    state = 28;
                    continue;
                } else {
                    lean_dec(v___y_7334_);
                    v___x_7359_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_7297_ = v___y_7331_;
                    v___y_7298_ = v___y_7332_;
                    v___y_7299_ = v___y_7333_;
                    v___y_7300_ = v___x_7353_;
                    v___y_7301_ = v___y_7335_;
                    v___y_7302_ = v___y_7336_;
                    v___y_7303_ = v___y_7337_;
                    v___y_7304_ = v___y_7338_;
                    v___y_7305_ = v___y_7339_;
                    v___y_7306_ = v___y_7340_;
                    v___y_7307_ = v___y_7341_;
                    v___y_7308_ = v___y_7342_;
                    v___y_7309_ = v___y_7344_;
                    v___y_7310_ = v___y_7343_;
                    v___y_7311_ = v___y_7345_;
                    v___y_7312_ = v___y_7346_;
                    v___y_7313_ = v___y_7347_;
                    v___y_7314_ = v___y_7349_;
                    v___y_7315_ = v___y_7350_;
                    v___y_7316_ = v___y_7348_;
                    v___y_7317_ = v___x_7359_;
                    state = 28;
                    continue;
                }
            }
            30 => {
                lean_inc_ref_n(v___y_7378_, 2);
                v___x_7381_ = l_Array_append___redArg(v___y_7378_, v___y_7380_);
                lean_dec_ref(v___y_7380_);
                lean_inc_n(v___y_7361_, 2);
                lean_inc_n(v___y_7363_, 2);
                v___x_7382_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7382_, 0, v___y_7363_);
                lean_ctor_set(v___x_7382_, 1, v___y_7361_);
                lean_ctor_set(v___x_7382_, 2, v___x_7381_);
                v___x_7383_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7383_, 0, v___y_7363_);
                lean_ctor_set(v___x_7383_, 1, v___y_7361_);
                lean_ctor_set(v___x_7383_, 2, v___y_7378_);
                v___x_7384_ = l_Lean_Syntax_node5(
                    v___y_7363_,
                    v___y_7370_,
                    v___y_7373_,
                    v___y_7369_,
                    v___y_7375_,
                    v___x_7382_,
                    v___x_7383_,
                );
                v___y_7147_ = v___y_7376_;
                v___y_7148_ = v___y_7367_;
                v___y_7149_ = v___y_7377_;
                v___y_7150_ = v___y_7379_;
                v_stxForSuggestion_7151_ = v___x_7384_;
                v___y_7152_ = v___y_7374_;
                v___y_7153_ = v___y_7365_;
                v___y_7154_ = v___y_7366_;
                v___y_7155_ = v___y_7362_;
                v___y_7156_ = v___y_7364_;
                v___y_7157_ = v___y_7371_;
                v___y_7158_ = v___y_7372_;
                v___y_7159_ = v___y_7368_;
                state = 21;
                continue;
            }
            31 => {
                lean_inc_ref(v___y_7403_);
                v___x_7406_ = l_Array_append___redArg(v___y_7403_, v___y_7405_);
                lean_dec_ref(v___y_7405_);
                lean_inc(v___y_7386_);
                lean_inc(v___y_7388_);
                v___x_7407_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7407_, 0, v___y_7388_);
                lean_ctor_set(v___x_7407_, 1, v___y_7386_);
                lean_ctor_set(v___x_7407_, 2, v___x_7406_);
                if lean_obj_tag(v___y_7390_) == 1 {
                    v_val_7408_ = lean_ctor_get(v___y_7390_, 0);
                    lean_inc(v_val_7408_);
                    lean_dec_ref_known(v___y_7390_, 1);
                    v___x_7409_ = l_Lean_SourceInfo_fromRef(v_val_7408_, v___x_7016_);
                    lean_dec(v_val_7408_);
                    v___x_7410_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_7411_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_7411_, 0, v___x_7409_);
                    lean_ctor_set(v___x_7411_, 1, v___x_7410_);
                    v___x_7412_ = l_Array_mkArray1___redArg(v___x_7411_);
                    v___y_7361_ = v___y_7386_;
                    v___y_7362_ = v___y_7387_;
                    v___y_7363_ = v___y_7388_;
                    v___y_7364_ = v___y_7389_;
                    v___y_7365_ = v___y_7391_;
                    v___y_7366_ = v___y_7392_;
                    v___y_7367_ = v___y_7393_;
                    v___y_7368_ = v___y_7394_;
                    v___y_7369_ = v___y_7395_;
                    v___y_7370_ = v___y_7396_;
                    v___y_7371_ = v___y_7397_;
                    v___y_7372_ = v___y_7399_;
                    v___y_7373_ = v___y_7398_;
                    v___y_7374_ = v___y_7400_;
                    v___y_7375_ = v___x_7407_;
                    v___y_7376_ = v___y_7401_;
                    v___y_7377_ = v___y_7402_;
                    v___y_7378_ = v___y_7403_;
                    v___y_7379_ = v___y_7404_;
                    v___y_7380_ = v___x_7412_;
                    state = 30;
                    continue;
                } else {
                    lean_dec(v___y_7390_);
                    v___x_7413_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_7361_ = v___y_7386_;
                    v___y_7362_ = v___y_7387_;
                    v___y_7363_ = v___y_7388_;
                    v___y_7364_ = v___y_7389_;
                    v___y_7365_ = v___y_7391_;
                    v___y_7366_ = v___y_7392_;
                    v___y_7367_ = v___y_7393_;
                    v___y_7368_ = v___y_7394_;
                    v___y_7369_ = v___y_7395_;
                    v___y_7370_ = v___y_7396_;
                    v___y_7371_ = v___y_7397_;
                    v___y_7372_ = v___y_7399_;
                    v___y_7373_ = v___y_7398_;
                    v___y_7374_ = v___y_7400_;
                    v___y_7375_ = v___x_7407_;
                    v___y_7376_ = v___y_7401_;
                    v___y_7377_ = v___y_7402_;
                    v___y_7378_ = v___y_7403_;
                    v___y_7379_ = v___y_7404_;
                    v___y_7380_ = v___x_7413_;
                    state = 30;
                    continue;
                }
            }
            32 => {
                v_ref_7431_ = lean_ctor_get(v___y_7425_, 5);
                v___x_7432_ = l_Lean_SourceInfo_fromRef(v_ref_7431_, v___y_7430_);
                v___x_7433_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7;
                v___x_7434_ =
                    l_Lean_Name_mkStr4(v___x_7017_, v___x_7018_, v___x_7019_, v___x_7433_);
                v___x_7435_ = l_Lean_SourceInfo_fromRef(v_tk_7032_, v___x_7016_);
                v___x_7436_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8;
                v___x_7437_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7437_, 0, v___x_7435_);
                lean_ctor_set(v___x_7437_, 1, v___x_7436_);
                v___x_7438_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                v___x_7439_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                if lean_obj_tag(v___y_7423_) == 1 {
                    v_val_7440_ = lean_ctor_get(v___y_7423_, 0);
                    lean_inc(v_val_7440_);
                    lean_dec_ref_known(v___y_7423_, 1);
                    v___x_7441_ = l_Array_mkArray1___redArg(v_val_7440_);
                    v___y_7204_ = v___y_7415_;
                    v___y_7205_ = v___y_7416_;
                    v___y_7206_ = v___y_7417_;
                    v___y_7207_ = v___x_7432_;
                    v___y_7208_ = v___y_7418_;
                    v___y_7209_ = v___y_7419_;
                    v___y_7210_ = v___y_7420_;
                    v___y_7211_ = v___y_7421_;
                    v___y_7212_ = v___x_7439_;
                    v___y_7213_ = v___y_7422_;
                    v___y_7214_ = v___y_7424_;
                    v___y_7215_ = v___x_7438_;
                    v___y_7216_ = v___x_7437_;
                    v___y_7217_ = v___y_7425_;
                    v___y_7218_ = v___y_7426_;
                    v___y_7219_ = v___y_7427_;
                    v___y_7220_ = v___x_7434_;
                    v___y_7221_ = v___y_7428_;
                    v___y_7222_ = v___y_7429_;
                    v___y_7223_ = v___x_7441_;
                    state = 25;
                    continue;
                } else {
                    lean_dec(v___y_7423_);
                    v___x_7442_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_7204_ = v___y_7415_;
                    v___y_7205_ = v___y_7416_;
                    v___y_7206_ = v___y_7417_;
                    v___y_7207_ = v___x_7432_;
                    v___y_7208_ = v___y_7418_;
                    v___y_7209_ = v___y_7419_;
                    v___y_7210_ = v___y_7420_;
                    v___y_7211_ = v___y_7421_;
                    v___y_7212_ = v___x_7439_;
                    v___y_7213_ = v___y_7422_;
                    v___y_7214_ = v___y_7424_;
                    v___y_7215_ = v___x_7438_;
                    v___y_7216_ = v___x_7437_;
                    v___y_7217_ = v___y_7425_;
                    v___y_7218_ = v___y_7426_;
                    v___y_7219_ = v___y_7427_;
                    v___y_7220_ = v___x_7434_;
                    v___y_7221_ = v___y_7428_;
                    v___y_7222_ = v___y_7429_;
                    v___y_7223_ = v___x_7442_;
                    state = 25;
                    continue;
                }
            }
            33 => {
                if v___y_7461_ == 0 {
                    v_ref_7462_ = lean_ctor_get(v___y_7456_, 5);
                    v___x_7463_ = l_Lean_SourceInfo_fromRef(v_ref_7462_, v___y_7461_);
                    v___x_7464_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7;
                    v___x_7465_ =
                        l_Lean_Name_mkStr4(v___x_7017_, v___x_7018_, v___x_7019_, v___x_7464_);
                    v___x_7466_ = l_Lean_SourceInfo_fromRef(v_tk_7032_, v___x_7016_);
                    v___x_7467_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8;
                    v___x_7468_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_7468_, 0, v___x_7466_);
                    lean_ctor_set(v___x_7468_, 1, v___x_7467_);
                    v___x_7469_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                    v___x_7470_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                    if lean_obj_tag(v___y_7454_) == 1 {
                        v_val_7471_ = lean_ctor_get(v___y_7454_, 0);
                        lean_inc(v_val_7471_);
                        lean_dec_ref_known(v___y_7454_, 1);
                        v___x_7472_ = l_Array_mkArray1___redArg(v_val_7471_);
                        v___y_7267_ = v___x_7469_;
                        v___y_7268_ = v___y_7445_;
                        v___y_7269_ = v___y_7446_;
                        v___y_7270_ = v___y_7447_;
                        v___y_7271_ = v___x_7470_;
                        v___y_7272_ = v___y_7448_;
                        v___y_7273_ = v___y_7449_;
                        v___y_7274_ = v___y_7450_;
                        v___y_7275_ = v___y_7451_;
                        v___y_7276_ = v___y_7452_;
                        v___y_7277_ = v___x_7465_;
                        v___y_7278_ = v___y_7453_;
                        v___y_7279_ = v___y_7455_;
                        v___y_7280_ = v___y_7456_;
                        v___y_7281_ = v___y_7457_;
                        v___y_7282_ = v___x_7463_;
                        v___y_7283_ = v___y_7458_;
                        v___y_7284_ = v___y_7459_;
                        v___y_7285_ = v___x_7468_;
                        v___y_7286_ = v___y_7460_;
                        v___y_7287_ = v___x_7472_;
                        state = 27;
                        continue;
                    } else {
                        lean_dec(v___y_7454_);
                        v___x_7473_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                        v___y_7267_ = v___x_7469_;
                        v___y_7268_ = v___y_7445_;
                        v___y_7269_ = v___y_7446_;
                        v___y_7270_ = v___y_7447_;
                        v___y_7271_ = v___x_7470_;
                        v___y_7272_ = v___y_7448_;
                        v___y_7273_ = v___y_7449_;
                        v___y_7274_ = v___y_7450_;
                        v___y_7275_ = v___y_7451_;
                        v___y_7276_ = v___y_7452_;
                        v___y_7277_ = v___x_7465_;
                        v___y_7278_ = v___y_7453_;
                        v___y_7279_ = v___y_7455_;
                        v___y_7280_ = v___y_7456_;
                        v___y_7281_ = v___y_7457_;
                        v___y_7282_ = v___x_7463_;
                        v___y_7283_ = v___y_7458_;
                        v___y_7284_ = v___y_7459_;
                        v___y_7285_ = v___x_7468_;
                        v___y_7286_ = v___y_7460_;
                        v___y_7287_ = v___x_7473_;
                        state = 27;
                        continue;
                    }
                } else {
                    v_ref_7474_ = lean_ctor_get(v___y_7456_, 5);
                    v___x_7475_ = l_Lean_SourceInfo_fromRef(v_ref_7474_, v___y_7444_);
                    v___x_7476_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9;
                    v___x_7477_ =
                        l_Lean_Name_mkStr4(v___x_7017_, v___x_7018_, v___x_7019_, v___x_7476_);
                    v___x_7478_ = l_Lean_SourceInfo_fromRef(v_tk_7032_, v___x_7016_);
                    v___x_7479_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10;
                    v___x_7480_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_7480_, 0, v___x_7478_);
                    lean_ctor_set(v___x_7480_, 1, v___x_7479_);
                    v___x_7481_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                    v___x_7482_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                    if lean_obj_tag(v___y_7454_) == 1 {
                        v_val_7483_ = lean_ctor_get(v___y_7454_, 0);
                        lean_inc(v_val_7483_);
                        lean_dec_ref_known(v___y_7454_, 1);
                        v___x_7484_ = l_Array_mkArray1___redArg(v_val_7483_);
                        v___y_7331_ = v___y_7445_;
                        v___y_7332_ = v___x_7475_;
                        v___y_7333_ = v___y_7446_;
                        v___y_7334_ = v___y_7447_;
                        v___y_7335_ = v___y_7448_;
                        v___y_7336_ = v___y_7449_;
                        v___y_7337_ = v___y_7450_;
                        v___y_7338_ = v___y_7451_;
                        v___y_7339_ = v___y_7452_;
                        v___y_7340_ = v___y_7453_;
                        v___y_7341_ = v___y_7455_;
                        v___y_7342_ = v___x_7482_;
                        v___y_7343_ = v___x_7480_;
                        v___y_7344_ = v___y_7456_;
                        v___y_7345_ = v___y_7457_;
                        v___y_7346_ = v___y_7458_;
                        v___y_7347_ = v___y_7459_;
                        v___y_7348_ = v___x_7477_;
                        v___y_7349_ = v___y_7460_;
                        v___y_7350_ = v___x_7481_;
                        v___y_7351_ = v___x_7484_;
                        state = 29;
                        continue;
                    } else {
                        lean_dec(v___y_7454_);
                        v___x_7485_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                        v___y_7331_ = v___y_7445_;
                        v___y_7332_ = v___x_7475_;
                        v___y_7333_ = v___y_7446_;
                        v___y_7334_ = v___y_7447_;
                        v___y_7335_ = v___y_7448_;
                        v___y_7336_ = v___y_7449_;
                        v___y_7337_ = v___y_7450_;
                        v___y_7338_ = v___y_7451_;
                        v___y_7339_ = v___y_7452_;
                        v___y_7340_ = v___y_7453_;
                        v___y_7341_ = v___y_7455_;
                        v___y_7342_ = v___x_7482_;
                        v___y_7343_ = v___x_7480_;
                        v___y_7344_ = v___y_7456_;
                        v___y_7345_ = v___y_7457_;
                        v___y_7346_ = v___y_7458_;
                        v___y_7347_ = v___y_7459_;
                        v___y_7348_ = v___x_7477_;
                        v___y_7349_ = v___y_7460_;
                        v___y_7350_ = v___x_7481_;
                        v___y_7351_ = v___x_7485_;
                        state = 29;
                        continue;
                    }
                }
            }
            34 => {
                v___x_7503_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg(
                    v___y_7488_,
                );
                v_a_7504_ = lean_ctor_get(v___x_7503_, 0);
                lean_inc(v_a_7504_);
                lean_dec_ref(v___x_7503_);
                v___x_7505_ = lean_array_get_size(v___y_7491_);
                v___x_7506_ = lean_nat_dec_eq(v___x_7505_, v___x_7031_);
                if v___x_7506_ == 0 {
                    if lean_obj_tag(v___y_7490_) == 0 {
                        v___y_7444_ = v___x_7506_;
                        v___y_7445_ = v___y_7498_;
                        v___y_7446_ = v___y_7499_;
                        v___y_7447_ = v___y_7489_;
                        v___y_7448_ = v___y_7496_;
                        v___y_7449_ = v___y_7497_;
                        v___y_7450_ = v___y_7492_;
                        v___y_7451_ = v___y_7491_;
                        v___y_7452_ = v___y_7502_;
                        v___y_7453_ = v_a_7504_;
                        v___y_7454_ = v___y_7487_;
                        v___y_7455_ = v___y_7500_;
                        v___y_7456_ = v___y_7501_;
                        v___y_7457_ = v___y_7495_;
                        v___y_7458_ = v___y_7490_;
                        v___y_7459_ = v_stxForExecution_7494_;
                        v___y_7460_ = v___y_7493_;
                        v___y_7461_ = v___x_7506_;
                        state = 33;
                        continue;
                    } else {
                        v___y_7444_ = v___x_7506_;
                        v___y_7445_ = v___y_7498_;
                        v___y_7446_ = v___y_7499_;
                        v___y_7447_ = v___y_7489_;
                        v___y_7448_ = v___y_7496_;
                        v___y_7449_ = v___y_7497_;
                        v___y_7450_ = v___y_7492_;
                        v___y_7451_ = v___y_7491_;
                        v___y_7452_ = v___y_7502_;
                        v___y_7453_ = v_a_7504_;
                        v___y_7454_ = v___y_7487_;
                        v___y_7455_ = v___y_7500_;
                        v___y_7456_ = v___y_7501_;
                        v___y_7457_ = v___y_7495_;
                        v___y_7458_ = v___y_7490_;
                        v___y_7459_ = v_stxForExecution_7494_;
                        v___y_7460_ = v___y_7493_;
                        v___y_7461_ = v___y_7493_;
                        state = 33;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_7491_);
                    if lean_obj_tag(v___y_7490_) == 0 {
                        v___x_7507_ = 0;
                        v___y_7415_ = v___y_7498_;
                        v___y_7416_ = v___y_7499_;
                        v___y_7417_ = v___y_7489_;
                        v___y_7418_ = v___y_7496_;
                        v___y_7419_ = v___y_7497_;
                        v___y_7420_ = v___y_7492_;
                        v___y_7421_ = v___y_7502_;
                        v___y_7422_ = v_a_7504_;
                        v___y_7423_ = v___y_7487_;
                        v___y_7424_ = v___y_7500_;
                        v___y_7425_ = v___y_7501_;
                        v___y_7426_ = v___y_7495_;
                        v___y_7427_ = v___y_7490_;
                        v___y_7428_ = v_stxForExecution_7494_;
                        v___y_7429_ = v___y_7493_;
                        v___y_7430_ = v___x_7507_;
                        state = 32;
                        continue;
                    } else {
                        if v___y_7493_ == 0 {
                            v___y_7415_ = v___y_7498_;
                            v___y_7416_ = v___y_7499_;
                            v___y_7417_ = v___y_7489_;
                            v___y_7418_ = v___y_7496_;
                            v___y_7419_ = v___y_7497_;
                            v___y_7420_ = v___y_7492_;
                            v___y_7421_ = v___y_7502_;
                            v___y_7422_ = v_a_7504_;
                            v___y_7423_ = v___y_7487_;
                            v___y_7424_ = v___y_7500_;
                            v___y_7425_ = v___y_7501_;
                            v___y_7426_ = v___y_7495_;
                            v___y_7427_ = v___y_7490_;
                            v___y_7428_ = v_stxForExecution_7494_;
                            v___y_7429_ = v___y_7493_;
                            v___y_7430_ = v___y_7493_;
                            state = 32;
                            continue;
                        } else {
                            v_ref_7508_ = lean_ctor_get(v___y_7501_, 5);
                            v___x_7509_ = 0;
                            v___x_7510_ = l_Lean_SourceInfo_fromRef(v_ref_7508_, v___x_7509_);
                            v___x_7511_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9;
                            v___x_7512_ = l_Lean_Name_mkStr4(
                                v___x_7017_,
                                v___x_7018_,
                                v___x_7019_,
                                v___x_7511_,
                            );
                            v___x_7513_ = l_Lean_SourceInfo_fromRef(v_tk_7032_, v___x_7016_);
                            v___x_7514_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10;
                            v___x_7515_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_7515_, 0, v___x_7513_);
                            lean_ctor_set(v___x_7515_, 1, v___x_7514_);
                            v___x_7516_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                            v___x_7517_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                            if lean_obj_tag(v___y_7487_) == 1 {
                                v_val_7518_ = lean_ctor_get(v___y_7487_, 0);
                                lean_inc(v_val_7518_);
                                lean_dec_ref_known(v___y_7487_, 1);
                                v___x_7519_ = l_Array_mkArray1___redArg(v_val_7518_);
                                v___y_7386_ = v___x_7516_;
                                v___y_7387_ = v___y_7498_;
                                v___y_7388_ = v___x_7510_;
                                v___y_7389_ = v___y_7499_;
                                v___y_7390_ = v___y_7489_;
                                v___y_7391_ = v___y_7496_;
                                v___y_7392_ = v___y_7497_;
                                v___y_7393_ = v___y_7492_;
                                v___y_7394_ = v___y_7502_;
                                v___y_7395_ = v_a_7504_;
                                v___y_7396_ = v___x_7512_;
                                v___y_7397_ = v___y_7500_;
                                v___y_7398_ = v___x_7515_;
                                v___y_7399_ = v___y_7501_;
                                v___y_7400_ = v___y_7495_;
                                v___y_7401_ = v___y_7490_;
                                v___y_7402_ = v_stxForExecution_7494_;
                                v___y_7403_ = v___x_7517_;
                                v___y_7404_ = v___y_7493_;
                                v___y_7405_ = v___x_7519_;
                                state = 31;
                                continue;
                            } else {
                                lean_dec(v___y_7487_);
                                v___x_7520_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                                v___y_7386_ = v___x_7516_;
                                v___y_7387_ = v___y_7498_;
                                v___y_7388_ = v___x_7510_;
                                v___y_7389_ = v___y_7499_;
                                v___y_7390_ = v___y_7489_;
                                v___y_7391_ = v___y_7496_;
                                v___y_7392_ = v___y_7497_;
                                v___y_7393_ = v___y_7492_;
                                v___y_7394_ = v___y_7502_;
                                v___y_7395_ = v_a_7504_;
                                v___y_7396_ = v___x_7512_;
                                v___y_7397_ = v___y_7500_;
                                v___y_7398_ = v___x_7515_;
                                v___y_7399_ = v___y_7501_;
                                v___y_7400_ = v___y_7495_;
                                v___y_7401_ = v___y_7490_;
                                v___y_7402_ = v_stxForExecution_7494_;
                                v___y_7403_ = v___x_7517_;
                                v___y_7404_ = v___y_7493_;
                                v___y_7405_ = v___x_7520_;
                                state = 31;
                                continue;
                            }
                        }
                    }
                }
            }
            35 => {
                lean_inc_ref_n(v___y_7536_, 2);
                v___x_7544_ = l_Array_append___redArg(v___y_7536_, v___y_7543_);
                lean_dec_ref(v___y_7543_);
                lean_inc_n(v___y_7529_, 2);
                lean_inc_n(v___y_7537_, 2);
                v___x_7545_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7545_, 0, v___y_7537_);
                lean_ctor_set(v___x_7545_, 1, v___y_7529_);
                lean_ctor_set(v___x_7545_, 2, v___x_7544_);
                v___x_7546_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7546_, 0, v___y_7537_);
                lean_ctor_set(v___x_7546_, 1, v___y_7529_);
                lean_ctor_set(v___x_7546_, 2, v___y_7536_);
                lean_inc(v___y_7522_);
                v___x_7547_ = l_Lean_Syntax_node5(
                    v___y_7537_,
                    v___y_7534_,
                    v___y_7524_,
                    v___y_7522_,
                    v___y_7523_,
                    v___x_7545_,
                    v___x_7546_,
                );
                v___y_7487_ = v___y_7532_;
                v___y_7488_ = v___y_7522_;
                v___y_7489_ = v___y_7526_;
                v___y_7490_ = v___y_7538_;
                v___y_7491_ = v___y_7531_;
                v___y_7492_ = v___y_7530_;
                v___y_7493_ = v___y_7542_;
                v_stxForExecution_7494_ = v___x_7547_;
                v___y_7495_ = v___y_7541_;
                v___y_7496_ = v___y_7525_;
                v___y_7497_ = v___y_7539_;
                v___y_7498_ = v___y_7527_;
                v___y_7499_ = v___y_7540_;
                v___y_7500_ = v___y_7528_;
                v___y_7501_ = v___y_7533_;
                v___y_7502_ = v___y_7535_;
                state = 34;
                continue;
            }
            36 => {
                lean_inc_ref(v___y_7562_);
                v___x_7570_ = l_Array_append___redArg(v___y_7562_, v___y_7569_);
                lean_dec_ref(v___y_7569_);
                lean_inc(v___y_7555_);
                lean_inc(v___y_7563_);
                v___x_7571_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7571_, 0, v___y_7563_);
                lean_ctor_set(v___x_7571_, 1, v___y_7555_);
                lean_ctor_set(v___x_7571_, 2, v___x_7570_);
                if lean_obj_tag(v___y_7552_) == 1 {
                    v_val_7572_ = lean_ctor_get(v___y_7552_, 0);
                    v___x_7573_ = l_Lean_SourceInfo_fromRef(v_val_7572_, v___x_7016_);
                    v___x_7574_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_7575_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_7575_, 0, v___x_7573_);
                    lean_ctor_set(v___x_7575_, 1, v___x_7574_);
                    v___x_7576_ = l_Array_mkArray1___redArg(v___x_7575_);
                    v___y_7522_ = v___y_7549_;
                    v___y_7523_ = v___x_7571_;
                    v___y_7524_ = v___y_7550_;
                    v___y_7525_ = v___y_7551_;
                    v___y_7526_ = v___y_7552_;
                    v___y_7527_ = v___y_7553_;
                    v___y_7528_ = v___y_7554_;
                    v___y_7529_ = v___y_7555_;
                    v___y_7530_ = v___y_7556_;
                    v___y_7531_ = v___y_7557_;
                    v___y_7532_ = v___y_7558_;
                    v___y_7533_ = v___y_7559_;
                    v___y_7534_ = v___y_7560_;
                    v___y_7535_ = v___y_7561_;
                    v___y_7536_ = v___y_7562_;
                    v___y_7537_ = v___y_7563_;
                    v___y_7538_ = v___y_7565_;
                    v___y_7539_ = v___y_7564_;
                    v___y_7540_ = v___y_7566_;
                    v___y_7541_ = v___y_7567_;
                    v___y_7542_ = v___y_7568_;
                    v___y_7543_ = v___x_7576_;
                    state = 35;
                    continue;
                } else {
                    v___x_7577_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_7522_ = v___y_7549_;
                    v___y_7523_ = v___x_7571_;
                    v___y_7524_ = v___y_7550_;
                    v___y_7525_ = v___y_7551_;
                    v___y_7526_ = v___y_7552_;
                    v___y_7527_ = v___y_7553_;
                    v___y_7528_ = v___y_7554_;
                    v___y_7529_ = v___y_7555_;
                    v___y_7530_ = v___y_7556_;
                    v___y_7531_ = v___y_7557_;
                    v___y_7532_ = v___y_7558_;
                    v___y_7533_ = v___y_7559_;
                    v___y_7534_ = v___y_7560_;
                    v___y_7535_ = v___y_7561_;
                    v___y_7536_ = v___y_7562_;
                    v___y_7537_ = v___y_7563_;
                    v___y_7538_ = v___y_7565_;
                    v___y_7539_ = v___y_7564_;
                    v___y_7540_ = v___y_7566_;
                    v___y_7541_ = v___y_7567_;
                    v___y_7542_ = v___y_7568_;
                    v___y_7543_ = v___x_7577_;
                    state = 35;
                    continue;
                }
            }
            37 => {
                lean_inc_ref_n(v___y_7592_, 2);
                v___x_7601_ = l_Array_append___redArg(v___y_7592_, v___y_7600_);
                lean_dec_ref(v___y_7600_);
                lean_inc_n(v___y_7590_, 3);
                lean_inc_n(v___y_7591_, 5);
                v___x_7602_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7602_, 0, v___y_7591_);
                lean_ctor_set(v___x_7602_, 1, v___y_7590_);
                lean_ctor_set(v___x_7602_, 2, v___x_7601_);
                v___x_7603_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
                v___x_7604_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7604_, 0, v___y_7591_);
                lean_ctor_set(v___x_7604_, 1, v___x_7603_);
                v___x_7605_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
                v___x_7606_ = l_Lean_Syntax_SepArray_ofElems(v___x_7605_, v___y_7586_);
                v___x_7607_ = l_Array_append___redArg(v___y_7592_, v___x_7606_);
                lean_dec_ref(v___x_7606_);
                v___x_7608_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7608_, 0, v___y_7591_);
                lean_ctor_set(v___x_7608_, 1, v___y_7590_);
                lean_ctor_set(v___x_7608_, 2, v___x_7607_);
                v___x_7609_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
                v___x_7610_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7610_, 0, v___y_7591_);
                lean_ctor_set(v___x_7610_, 1, v___x_7609_);
                v___x_7611_ = l_Lean_Syntax_node3(
                    v___y_7591_,
                    v___y_7590_,
                    v___x_7604_,
                    v___x_7608_,
                    v___x_7610_,
                );
                lean_inc(v___y_7579_);
                v___x_7612_ = l_Lean_Syntax_node5(
                    v___y_7591_,
                    v___y_7595_,
                    v___y_7587_,
                    v___y_7579_,
                    v___y_7582_,
                    v___x_7602_,
                    v___x_7611_,
                );
                v___y_7487_ = v___y_7588_;
                v___y_7488_ = v___y_7579_;
                v___y_7489_ = v___y_7581_;
                v___y_7490_ = v___y_7594_;
                v___y_7491_ = v___y_7586_;
                v___y_7492_ = v___y_7585_;
                v___y_7493_ = v___y_7599_;
                v_stxForExecution_7494_ = v___x_7612_;
                v___y_7495_ = v___y_7598_;
                v___y_7496_ = v___y_7580_;
                v___y_7497_ = v___y_7596_;
                v___y_7498_ = v___y_7583_;
                v___y_7499_ = v___y_7597_;
                v___y_7500_ = v___y_7584_;
                v___y_7501_ = v___y_7589_;
                v___y_7502_ = v___y_7593_;
                state = 34;
                continue;
            }
            38 => {
                lean_inc_ref(v___y_7626_);
                v___x_7635_ = l_Array_append___redArg(v___y_7626_, v___y_7634_);
                lean_dec_ref(v___y_7634_);
                lean_inc(v___y_7624_);
                lean_inc(v___y_7625_);
                v___x_7636_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7636_, 0, v___y_7625_);
                lean_ctor_set(v___x_7636_, 1, v___y_7624_);
                lean_ctor_set(v___x_7636_, 2, v___x_7635_);
                if lean_obj_tag(v___y_7616_) == 1 {
                    v_val_7637_ = lean_ctor_get(v___y_7616_, 0);
                    v___x_7638_ = l_Lean_SourceInfo_fromRef(v_val_7637_, v___x_7016_);
                    v___x_7639_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_7640_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_7640_, 0, v___x_7638_);
                    lean_ctor_set(v___x_7640_, 1, v___x_7639_);
                    v___x_7641_ = l_Array_mkArray1___redArg(v___x_7640_);
                    v___y_7579_ = v___y_7614_;
                    v___y_7580_ = v___y_7615_;
                    v___y_7581_ = v___y_7616_;
                    v___y_7582_ = v___x_7636_;
                    v___y_7583_ = v___y_7617_;
                    v___y_7584_ = v___y_7618_;
                    v___y_7585_ = v___y_7619_;
                    v___y_7586_ = v___y_7620_;
                    v___y_7587_ = v___y_7621_;
                    v___y_7588_ = v___y_7622_;
                    v___y_7589_ = v___y_7623_;
                    v___y_7590_ = v___y_7624_;
                    v___y_7591_ = v___y_7625_;
                    v___y_7592_ = v___y_7626_;
                    v___y_7593_ = v___y_7627_;
                    v___y_7594_ = v___y_7630_;
                    v___y_7595_ = v___y_7629_;
                    v___y_7596_ = v___y_7628_;
                    v___y_7597_ = v___y_7631_;
                    v___y_7598_ = v___y_7632_;
                    v___y_7599_ = v___y_7633_;
                    v___y_7600_ = v___x_7641_;
                    state = 37;
                    continue;
                } else {
                    v___x_7642_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_7579_ = v___y_7614_;
                    v___y_7580_ = v___y_7615_;
                    v___y_7581_ = v___y_7616_;
                    v___y_7582_ = v___x_7636_;
                    v___y_7583_ = v___y_7617_;
                    v___y_7584_ = v___y_7618_;
                    v___y_7585_ = v___y_7619_;
                    v___y_7586_ = v___y_7620_;
                    v___y_7587_ = v___y_7621_;
                    v___y_7588_ = v___y_7622_;
                    v___y_7589_ = v___y_7623_;
                    v___y_7590_ = v___y_7624_;
                    v___y_7591_ = v___y_7625_;
                    v___y_7592_ = v___y_7626_;
                    v___y_7593_ = v___y_7627_;
                    v___y_7594_ = v___y_7630_;
                    v___y_7595_ = v___y_7629_;
                    v___y_7596_ = v___y_7628_;
                    v___y_7597_ = v___y_7631_;
                    v___y_7598_ = v___y_7632_;
                    v___y_7599_ = v___y_7633_;
                    v___y_7600_ = v___x_7642_;
                    state = 37;
                    continue;
                }
            }
            39 => {
                lean_inc_ref_n(v___y_7650_, 2);
                v___x_7666_ = l_Array_append___redArg(v___y_7650_, v___y_7665_);
                lean_dec_ref(v___y_7665_);
                lean_inc_n(v___y_7647_, 3);
                lean_inc_n(v___y_7655_, 5);
                v___x_7667_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7667_, 0, v___y_7655_);
                lean_ctor_set(v___x_7667_, 1, v___y_7647_);
                lean_ctor_set(v___x_7667_, 2, v___x_7666_);
                v___x_7668_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
                v___x_7669_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7669_, 0, v___y_7655_);
                lean_ctor_set(v___x_7669_, 1, v___x_7668_);
                v___x_7670_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
                v___x_7671_ = l_Lean_Syntax_SepArray_ofElems(v___x_7670_, v___y_7652_);
                v___x_7672_ = l_Array_append___redArg(v___y_7650_, v___x_7671_);
                lean_dec_ref(v___x_7671_);
                v___x_7673_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7673_, 0, v___y_7655_);
                lean_ctor_set(v___x_7673_, 1, v___y_7647_);
                lean_ctor_set(v___x_7673_, 2, v___x_7672_);
                v___x_7674_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
                v___x_7675_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7675_, 0, v___y_7655_);
                lean_ctor_set(v___x_7675_, 1, v___x_7674_);
                v___x_7676_ = l_Lean_Syntax_node3(
                    v___y_7655_,
                    v___y_7647_,
                    v___x_7669_,
                    v___x_7673_,
                    v___x_7675_,
                );
                lean_inc(v___y_7644_);
                v___x_7677_ = l_Lean_Syntax_node5(
                    v___y_7655_,
                    v___y_7657_,
                    v___y_7661_,
                    v___y_7644_,
                    v___y_7662_,
                    v___x_7667_,
                    v___x_7676_,
                );
                v___y_7487_ = v___y_7653_;
                v___y_7488_ = v___y_7644_;
                v___y_7489_ = v___y_7646_;
                v___y_7490_ = v___y_7658_;
                v___y_7491_ = v___y_7652_;
                v___y_7492_ = v___y_7651_;
                v___y_7493_ = v___y_7664_;
                v_stxForExecution_7494_ = v___x_7677_;
                v___y_7495_ = v___y_7663_;
                v___y_7496_ = v___y_7645_;
                v___y_7497_ = v___y_7659_;
                v___y_7498_ = v___y_7648_;
                v___y_7499_ = v___y_7660_;
                v___y_7500_ = v___y_7649_;
                v___y_7501_ = v___y_7654_;
                v___y_7502_ = v___y_7656_;
                state = 34;
                continue;
            }
            40 => {
                lean_inc_ref(v___y_7685_);
                v___x_7700_ = l_Array_append___redArg(v___y_7685_, v___y_7699_);
                lean_dec_ref(v___y_7699_);
                lean_inc(v___y_7682_);
                lean_inc(v___y_7690_);
                v___x_7701_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7701_, 0, v___y_7690_);
                lean_ctor_set(v___x_7701_, 1, v___y_7682_);
                lean_ctor_set(v___x_7701_, 2, v___x_7700_);
                if lean_obj_tag(v___y_7681_) == 1 {
                    v_val_7702_ = lean_ctor_get(v___y_7681_, 0);
                    v___x_7703_ = l_Lean_SourceInfo_fromRef(v_val_7702_, v___x_7016_);
                    v___x_7704_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_7705_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_7705_, 0, v___x_7703_);
                    lean_ctor_set(v___x_7705_, 1, v___x_7704_);
                    v___x_7706_ = l_Array_mkArray1___redArg(v___x_7705_);
                    v___y_7644_ = v___y_7679_;
                    v___y_7645_ = v___y_7680_;
                    v___y_7646_ = v___y_7681_;
                    v___y_7647_ = v___y_7682_;
                    v___y_7648_ = v___y_7683_;
                    v___y_7649_ = v___y_7684_;
                    v___y_7650_ = v___y_7685_;
                    v___y_7651_ = v___y_7686_;
                    v___y_7652_ = v___y_7687_;
                    v___y_7653_ = v___y_7688_;
                    v___y_7654_ = v___y_7689_;
                    v___y_7655_ = v___y_7690_;
                    v___y_7656_ = v___y_7691_;
                    v___y_7657_ = v___y_7692_;
                    v___y_7658_ = v___y_7694_;
                    v___y_7659_ = v___y_7693_;
                    v___y_7660_ = v___y_7695_;
                    v___y_7661_ = v___y_7697_;
                    v___y_7662_ = v___x_7701_;
                    v___y_7663_ = v___y_7696_;
                    v___y_7664_ = v___y_7698_;
                    v___y_7665_ = v___x_7706_;
                    state = 39;
                    continue;
                } else {
                    v___x_7707_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_7644_ = v___y_7679_;
                    v___y_7645_ = v___y_7680_;
                    v___y_7646_ = v___y_7681_;
                    v___y_7647_ = v___y_7682_;
                    v___y_7648_ = v___y_7683_;
                    v___y_7649_ = v___y_7684_;
                    v___y_7650_ = v___y_7685_;
                    v___y_7651_ = v___y_7686_;
                    v___y_7652_ = v___y_7687_;
                    v___y_7653_ = v___y_7688_;
                    v___y_7654_ = v___y_7689_;
                    v___y_7655_ = v___y_7690_;
                    v___y_7656_ = v___y_7691_;
                    v___y_7657_ = v___y_7692_;
                    v___y_7658_ = v___y_7694_;
                    v___y_7659_ = v___y_7693_;
                    v___y_7660_ = v___y_7695_;
                    v___y_7661_ = v___y_7697_;
                    v___y_7662_ = v___x_7701_;
                    v___y_7663_ = v___y_7696_;
                    v___y_7664_ = v___y_7698_;
                    v___y_7665_ = v___x_7707_;
                    state = 39;
                    continue;
                }
            }
            41 => {
                lean_inc_ref_n(v___y_7718_, 2);
                v___x_7731_ = l_Array_append___redArg(v___y_7718_, v___y_7730_);
                lean_dec_ref(v___y_7730_);
                lean_inc_n(v___y_7719_, 2);
                lean_inc_n(v___y_7710_, 2);
                v___x_7732_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7732_, 0, v___y_7710_);
                lean_ctor_set(v___x_7732_, 1, v___y_7719_);
                lean_ctor_set(v___x_7732_, 2, v___x_7731_);
                v___x_7733_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7733_, 0, v___y_7710_);
                lean_ctor_set(v___x_7733_, 1, v___y_7719_);
                lean_ctor_set(v___x_7733_, 2, v___y_7718_);
                lean_inc(v___y_7709_);
                v___x_7734_ = l_Lean_Syntax_node5(
                    v___y_7710_,
                    v___y_7723_,
                    v___y_7726_,
                    v___y_7709_,
                    v___y_7712_,
                    v___x_7732_,
                    v___x_7733_,
                );
                v___y_7487_ = v___y_7720_;
                v___y_7488_ = v___y_7709_;
                v___y_7489_ = v___y_7713_;
                v___y_7490_ = v___y_7724_;
                v___y_7491_ = v___y_7717_;
                v___y_7492_ = v___y_7716_;
                v___y_7493_ = v___y_7729_;
                v_stxForExecution_7494_ = v___x_7734_;
                v___y_7495_ = v___y_7728_;
                v___y_7496_ = v___y_7711_;
                v___y_7497_ = v___y_7725_;
                v___y_7498_ = v___y_7714_;
                v___y_7499_ = v___y_7727_;
                v___y_7500_ = v___y_7715_;
                v___y_7501_ = v___y_7721_;
                v___y_7502_ = v___y_7722_;
                state = 34;
                continue;
            }
            42 => {
                lean_inc_ref(v___y_7744_);
                v___x_7757_ = l_Array_append___redArg(v___y_7744_, v___y_7756_);
                lean_dec_ref(v___y_7756_);
                lean_inc(v___y_7745_);
                lean_inc(v___y_7737_);
                v___x_7758_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7758_, 0, v___y_7737_);
                lean_ctor_set(v___x_7758_, 1, v___y_7745_);
                lean_ctor_set(v___x_7758_, 2, v___x_7757_);
                if lean_obj_tag(v___y_7739_) == 1 {
                    v_val_7759_ = lean_ctor_get(v___y_7739_, 0);
                    v___x_7760_ = l_Lean_SourceInfo_fromRef(v_val_7759_, v___x_7016_);
                    v___x_7761_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_7762_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_7762_, 0, v___x_7760_);
                    lean_ctor_set(v___x_7762_, 1, v___x_7761_);
                    v___x_7763_ = l_Array_mkArray1___redArg(v___x_7762_);
                    v___y_7709_ = v___y_7736_;
                    v___y_7710_ = v___y_7737_;
                    v___y_7711_ = v___y_7738_;
                    v___y_7712_ = v___x_7758_;
                    v___y_7713_ = v___y_7739_;
                    v___y_7714_ = v___y_7740_;
                    v___y_7715_ = v___y_7741_;
                    v___y_7716_ = v___y_7742_;
                    v___y_7717_ = v___y_7743_;
                    v___y_7718_ = v___y_7744_;
                    v___y_7719_ = v___y_7745_;
                    v___y_7720_ = v___y_7746_;
                    v___y_7721_ = v___y_7747_;
                    v___y_7722_ = v___y_7749_;
                    v___y_7723_ = v___y_7748_;
                    v___y_7724_ = v___y_7751_;
                    v___y_7725_ = v___y_7750_;
                    v___y_7726_ = v___y_7753_;
                    v___y_7727_ = v___y_7752_;
                    v___y_7728_ = v___y_7754_;
                    v___y_7729_ = v___y_7755_;
                    v___y_7730_ = v___x_7763_;
                    state = 41;
                    continue;
                } else {
                    v___x_7764_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_7709_ = v___y_7736_;
                    v___y_7710_ = v___y_7737_;
                    v___y_7711_ = v___y_7738_;
                    v___y_7712_ = v___x_7758_;
                    v___y_7713_ = v___y_7739_;
                    v___y_7714_ = v___y_7740_;
                    v___y_7715_ = v___y_7741_;
                    v___y_7716_ = v___y_7742_;
                    v___y_7717_ = v___y_7743_;
                    v___y_7718_ = v___y_7744_;
                    v___y_7719_ = v___y_7745_;
                    v___y_7720_ = v___y_7746_;
                    v___y_7721_ = v___y_7747_;
                    v___y_7722_ = v___y_7749_;
                    v___y_7723_ = v___y_7748_;
                    v___y_7724_ = v___y_7751_;
                    v___y_7725_ = v___y_7750_;
                    v___y_7726_ = v___y_7753_;
                    v___y_7727_ = v___y_7752_;
                    v___y_7728_ = v___y_7754_;
                    v___y_7729_ = v___y_7755_;
                    v___y_7730_ = v___x_7764_;
                    state = 41;
                    continue;
                }
            }
            43 => {
                v_ref_7782_ = lean_ctor_get(v___y_7774_, 5);
                v___x_7783_ = l_Lean_SourceInfo_fromRef(v_ref_7782_, v___y_7781_);
                v___x_7784_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7;
                lean_inc_ref(v___x_7019_);
                lean_inc_ref(v___x_7018_);
                lean_inc_ref(v___x_7017_);
                v___x_7785_ =
                    l_Lean_Name_mkStr4(v___x_7017_, v___x_7018_, v___x_7019_, v___x_7784_);
                v___x_7786_ = l_Lean_SourceInfo_fromRef(v_tk_7032_, v___x_7016_);
                v___x_7787_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8;
                v___x_7788_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7788_, 0, v___x_7786_);
                lean_ctor_set(v___x_7788_, 1, v___x_7787_);
                v___x_7789_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                v___x_7790_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                if lean_obj_tag(v___y_7773_) == 1 {
                    v_val_7791_ = lean_ctor_get(v___y_7773_, 0);
                    lean_inc(v_val_7791_);
                    v___x_7792_ = l_Array_mkArray1___redArg(v_val_7791_);
                    v___y_7549_ = v___y_7766_;
                    v___y_7550_ = v___x_7788_;
                    v___y_7551_ = v___y_7767_;
                    v___y_7552_ = v___y_7768_;
                    v___y_7553_ = v___y_7769_;
                    v___y_7554_ = v___y_7770_;
                    v___y_7555_ = v___x_7789_;
                    v___y_7556_ = v___y_7771_;
                    v___y_7557_ = v___y_7772_;
                    v___y_7558_ = v___y_7773_;
                    v___y_7559_ = v___y_7774_;
                    v___y_7560_ = v___x_7785_;
                    v___y_7561_ = v___y_7775_;
                    v___y_7562_ = v___x_7790_;
                    v___y_7563_ = v___x_7783_;
                    v___y_7564_ = v___y_7776_;
                    v___y_7565_ = v___y_7777_;
                    v___y_7566_ = v___y_7778_;
                    v___y_7567_ = v___y_7779_;
                    v___y_7568_ = v___y_7780_;
                    v___y_7569_ = v___x_7792_;
                    state = 36;
                    continue;
                } else {
                    v___x_7793_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_7549_ = v___y_7766_;
                    v___y_7550_ = v___x_7788_;
                    v___y_7551_ = v___y_7767_;
                    v___y_7552_ = v___y_7768_;
                    v___y_7553_ = v___y_7769_;
                    v___y_7554_ = v___y_7770_;
                    v___y_7555_ = v___x_7789_;
                    v___y_7556_ = v___y_7771_;
                    v___y_7557_ = v___y_7772_;
                    v___y_7558_ = v___y_7773_;
                    v___y_7559_ = v___y_7774_;
                    v___y_7560_ = v___x_7785_;
                    v___y_7561_ = v___y_7775_;
                    v___y_7562_ = v___x_7790_;
                    v___y_7563_ = v___x_7783_;
                    v___y_7564_ = v___y_7776_;
                    v___y_7565_ = v___y_7777_;
                    v___y_7566_ = v___y_7778_;
                    v___y_7567_ = v___y_7779_;
                    v___y_7568_ = v___y_7780_;
                    v___y_7569_ = v___x_7793_;
                    state = 36;
                    continue;
                }
            }
            44 => {
                if v___y_7811_ == 0 {
                    v_ref_7812_ = lean_ctor_get(v___y_7803_, 5);
                    v___x_7813_ = l_Lean_SourceInfo_fromRef(v_ref_7812_, v___y_7811_);
                    v___x_7814_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__7;
                    lean_inc_ref(v___x_7019_);
                    lean_inc_ref(v___x_7018_);
                    lean_inc_ref(v___x_7017_);
                    v___x_7815_ =
                        l_Lean_Name_mkStr4(v___x_7017_, v___x_7018_, v___x_7019_, v___x_7814_);
                    v___x_7816_ = l_Lean_SourceInfo_fromRef(v_tk_7032_, v___x_7016_);
                    v___x_7817_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__8;
                    v___x_7818_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_7818_, 0, v___x_7816_);
                    lean_ctor_set(v___x_7818_, 1, v___x_7817_);
                    v___x_7819_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                    v___x_7820_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                    if lean_obj_tag(v___y_7802_) == 1 {
                        v_val_7821_ = lean_ctor_get(v___y_7802_, 0);
                        lean_inc(v_val_7821_);
                        v___x_7822_ = l_Array_mkArray1___redArg(v_val_7821_);
                        v___y_7614_ = v___y_7795_;
                        v___y_7615_ = v___y_7796_;
                        v___y_7616_ = v___y_7797_;
                        v___y_7617_ = v___y_7798_;
                        v___y_7618_ = v___y_7799_;
                        v___y_7619_ = v___y_7800_;
                        v___y_7620_ = v___y_7801_;
                        v___y_7621_ = v___x_7818_;
                        v___y_7622_ = v___y_7802_;
                        v___y_7623_ = v___y_7803_;
                        v___y_7624_ = v___x_7819_;
                        v___y_7625_ = v___x_7813_;
                        v___y_7626_ = v___x_7820_;
                        v___y_7627_ = v___y_7805_;
                        v___y_7628_ = v___y_7806_;
                        v___y_7629_ = v___x_7815_;
                        v___y_7630_ = v___y_7807_;
                        v___y_7631_ = v___y_7808_;
                        v___y_7632_ = v___y_7809_;
                        v___y_7633_ = v___y_7810_;
                        v___y_7634_ = v___x_7822_;
                        state = 38;
                        continue;
                    } else {
                        v___x_7823_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                        v___y_7614_ = v___y_7795_;
                        v___y_7615_ = v___y_7796_;
                        v___y_7616_ = v___y_7797_;
                        v___y_7617_ = v___y_7798_;
                        v___y_7618_ = v___y_7799_;
                        v___y_7619_ = v___y_7800_;
                        v___y_7620_ = v___y_7801_;
                        v___y_7621_ = v___x_7818_;
                        v___y_7622_ = v___y_7802_;
                        v___y_7623_ = v___y_7803_;
                        v___y_7624_ = v___x_7819_;
                        v___y_7625_ = v___x_7813_;
                        v___y_7626_ = v___x_7820_;
                        v___y_7627_ = v___y_7805_;
                        v___y_7628_ = v___y_7806_;
                        v___y_7629_ = v___x_7815_;
                        v___y_7630_ = v___y_7807_;
                        v___y_7631_ = v___y_7808_;
                        v___y_7632_ = v___y_7809_;
                        v___y_7633_ = v___y_7810_;
                        v___y_7634_ = v___x_7823_;
                        state = 38;
                        continue;
                    }
                } else {
                    v_ref_7824_ = lean_ctor_get(v___y_7803_, 5);
                    v___x_7825_ = l_Lean_SourceInfo_fromRef(v_ref_7824_, v___y_7804_);
                    v___x_7826_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9;
                    lean_inc_ref(v___x_7019_);
                    lean_inc_ref(v___x_7018_);
                    lean_inc_ref(v___x_7017_);
                    v___x_7827_ =
                        l_Lean_Name_mkStr4(v___x_7017_, v___x_7018_, v___x_7019_, v___x_7826_);
                    v___x_7828_ = l_Lean_SourceInfo_fromRef(v_tk_7032_, v___x_7016_);
                    v___x_7829_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10;
                    v___x_7830_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_7830_, 0, v___x_7828_);
                    lean_ctor_set(v___x_7830_, 1, v___x_7829_);
                    v___x_7831_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                    v___x_7832_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                    if lean_obj_tag(v___y_7802_) == 1 {
                        v_val_7833_ = lean_ctor_get(v___y_7802_, 0);
                        lean_inc(v_val_7833_);
                        v___x_7834_ = l_Array_mkArray1___redArg(v_val_7833_);
                        v___y_7679_ = v___y_7795_;
                        v___y_7680_ = v___y_7796_;
                        v___y_7681_ = v___y_7797_;
                        v___y_7682_ = v___x_7831_;
                        v___y_7683_ = v___y_7798_;
                        v___y_7684_ = v___y_7799_;
                        v___y_7685_ = v___x_7832_;
                        v___y_7686_ = v___y_7800_;
                        v___y_7687_ = v___y_7801_;
                        v___y_7688_ = v___y_7802_;
                        v___y_7689_ = v___y_7803_;
                        v___y_7690_ = v___x_7825_;
                        v___y_7691_ = v___y_7805_;
                        v___y_7692_ = v___x_7827_;
                        v___y_7693_ = v___y_7806_;
                        v___y_7694_ = v___y_7807_;
                        v___y_7695_ = v___y_7808_;
                        v___y_7696_ = v___y_7809_;
                        v___y_7697_ = v___x_7830_;
                        v___y_7698_ = v___y_7810_;
                        v___y_7699_ = v___x_7834_;
                        state = 40;
                        continue;
                    } else {
                        v___x_7835_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                        v___y_7679_ = v___y_7795_;
                        v___y_7680_ = v___y_7796_;
                        v___y_7681_ = v___y_7797_;
                        v___y_7682_ = v___x_7831_;
                        v___y_7683_ = v___y_7798_;
                        v___y_7684_ = v___y_7799_;
                        v___y_7685_ = v___x_7832_;
                        v___y_7686_ = v___y_7800_;
                        v___y_7687_ = v___y_7801_;
                        v___y_7688_ = v___y_7802_;
                        v___y_7689_ = v___y_7803_;
                        v___y_7690_ = v___x_7825_;
                        v___y_7691_ = v___y_7805_;
                        v___y_7692_ = v___x_7827_;
                        v___y_7693_ = v___y_7806_;
                        v___y_7694_ = v___y_7807_;
                        v___y_7695_ = v___y_7808_;
                        v___y_7696_ = v___y_7809_;
                        v___y_7697_ = v___x_7830_;
                        v___y_7698_ = v___y_7810_;
                        v___y_7699_ = v___x_7835_;
                        state = 40;
                        continue;
                    }
                }
            }
            45 => {
                v___x_7852_ = lean_array_get_size(v_argsArray_7843_);
                v___x_7853_ = lean_nat_dec_eq(v___x_7852_, v___x_7031_);
                if v___x_7853_ == 0 {
                    if lean_obj_tag(v___y_7840_) == 0 {
                        v___y_7795_ = v___y_7837_;
                        v___y_7796_ = v___y_7845_;
                        v___y_7797_ = v___y_7839_;
                        v___y_7798_ = v___y_7847_;
                        v___y_7799_ = v___y_7849_;
                        v___y_7800_ = v___y_7841_;
                        v___y_7801_ = v_argsArray_7843_;
                        v___y_7802_ = v___y_7838_;
                        v___y_7803_ = v___y_7850_;
                        v___y_7804_ = v___x_7853_;
                        v___y_7805_ = v___y_7851_;
                        v___y_7806_ = v___y_7846_;
                        v___y_7807_ = v___y_7840_;
                        v___y_7808_ = v___y_7848_;
                        v___y_7809_ = v___y_7844_;
                        v___y_7810_ = v___y_7842_;
                        v___y_7811_ = v___x_7853_;
                        state = 44;
                        continue;
                    } else {
                        v___y_7795_ = v___y_7837_;
                        v___y_7796_ = v___y_7845_;
                        v___y_7797_ = v___y_7839_;
                        v___y_7798_ = v___y_7847_;
                        v___y_7799_ = v___y_7849_;
                        v___y_7800_ = v___y_7841_;
                        v___y_7801_ = v_argsArray_7843_;
                        v___y_7802_ = v___y_7838_;
                        v___y_7803_ = v___y_7850_;
                        v___y_7804_ = v___x_7853_;
                        v___y_7805_ = v___y_7851_;
                        v___y_7806_ = v___y_7846_;
                        v___y_7807_ = v___y_7840_;
                        v___y_7808_ = v___y_7848_;
                        v___y_7809_ = v___y_7844_;
                        v___y_7810_ = v___y_7842_;
                        v___y_7811_ = v___y_7842_;
                        state = 44;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___y_7840_) == 0 {
                        v___x_7854_ = 0;
                        v___y_7766_ = v___y_7837_;
                        v___y_7767_ = v___y_7845_;
                        v___y_7768_ = v___y_7839_;
                        v___y_7769_ = v___y_7847_;
                        v___y_7770_ = v___y_7849_;
                        v___y_7771_ = v___y_7841_;
                        v___y_7772_ = v_argsArray_7843_;
                        v___y_7773_ = v___y_7838_;
                        v___y_7774_ = v___y_7850_;
                        v___y_7775_ = v___y_7851_;
                        v___y_7776_ = v___y_7846_;
                        v___y_7777_ = v___y_7840_;
                        v___y_7778_ = v___y_7848_;
                        v___y_7779_ = v___y_7844_;
                        v___y_7780_ = v___y_7842_;
                        v___y_7781_ = v___x_7854_;
                        state = 43;
                        continue;
                    } else {
                        if v___y_7842_ == 0 {
                            v___y_7766_ = v___y_7837_;
                            v___y_7767_ = v___y_7845_;
                            v___y_7768_ = v___y_7839_;
                            v___y_7769_ = v___y_7847_;
                            v___y_7770_ = v___y_7849_;
                            v___y_7771_ = v___y_7841_;
                            v___y_7772_ = v_argsArray_7843_;
                            v___y_7773_ = v___y_7838_;
                            v___y_7774_ = v___y_7850_;
                            v___y_7775_ = v___y_7851_;
                            v___y_7776_ = v___y_7846_;
                            v___y_7777_ = v___y_7840_;
                            v___y_7778_ = v___y_7848_;
                            v___y_7779_ = v___y_7844_;
                            v___y_7780_ = v___y_7842_;
                            v___y_7781_ = v___y_7842_;
                            state = 43;
                            continue;
                        } else {
                            v_ref_7855_ = lean_ctor_get(v___y_7850_, 5);
                            v___x_7856_ = 0;
                            v___x_7857_ = l_Lean_SourceInfo_fromRef(v_ref_7855_, v___x_7856_);
                            v___x_7858_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__9;
                            lean_inc_ref(v___x_7019_);
                            lean_inc_ref(v___x_7018_);
                            lean_inc_ref(v___x_7017_);
                            v___x_7859_ = l_Lean_Name_mkStr4(
                                v___x_7017_,
                                v___x_7018_,
                                v___x_7019_,
                                v___x_7858_,
                            );
                            v___x_7860_ = l_Lean_SourceInfo_fromRef(v_tk_7032_, v___x_7016_);
                            v___x_7861_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__10;
                            v___x_7862_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_7862_, 0, v___x_7860_);
                            lean_ctor_set(v___x_7862_, 1, v___x_7861_);
                            v___x_7863_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                            v___x_7864_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                            if lean_obj_tag(v___y_7838_) == 1 {
                                v_val_7865_ = lean_ctor_get(v___y_7838_, 0);
                                lean_inc(v_val_7865_);
                                v___x_7866_ = l_Array_mkArray1___redArg(v_val_7865_);
                                v___y_7736_ = v___y_7837_;
                                v___y_7737_ = v___x_7857_;
                                v___y_7738_ = v___y_7845_;
                                v___y_7739_ = v___y_7839_;
                                v___y_7740_ = v___y_7847_;
                                v___y_7741_ = v___y_7849_;
                                v___y_7742_ = v___y_7841_;
                                v___y_7743_ = v_argsArray_7843_;
                                v___y_7744_ = v___x_7864_;
                                v___y_7745_ = v___x_7863_;
                                v___y_7746_ = v___y_7838_;
                                v___y_7747_ = v___y_7850_;
                                v___y_7748_ = v___x_7859_;
                                v___y_7749_ = v___y_7851_;
                                v___y_7750_ = v___y_7846_;
                                v___y_7751_ = v___y_7840_;
                                v___y_7752_ = v___y_7848_;
                                v___y_7753_ = v___x_7862_;
                                v___y_7754_ = v___y_7844_;
                                v___y_7755_ = v___y_7842_;
                                v___y_7756_ = v___x_7866_;
                                state = 42;
                                continue;
                            } else {
                                v___x_7867_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                                v___y_7736_ = v___y_7837_;
                                v___y_7737_ = v___x_7857_;
                                v___y_7738_ = v___y_7845_;
                                v___y_7739_ = v___y_7839_;
                                v___y_7740_ = v___y_7847_;
                                v___y_7741_ = v___y_7849_;
                                v___y_7742_ = v___y_7841_;
                                v___y_7743_ = v_argsArray_7843_;
                                v___y_7744_ = v___x_7864_;
                                v___y_7745_ = v___x_7863_;
                                v___y_7746_ = v___y_7838_;
                                v___y_7747_ = v___y_7850_;
                                v___y_7748_ = v___x_7859_;
                                v___y_7749_ = v___y_7851_;
                                v___y_7750_ = v___y_7846_;
                                v___y_7751_ = v___y_7840_;
                                v___y_7752_ = v___y_7848_;
                                v___y_7753_ = v___x_7862_;
                                v___y_7754_ = v___y_7844_;
                                v___y_7755_ = v___y_7842_;
                                v___y_7756_ = v___x_7867_;
                                state = 42;
                                continue;
                            }
                        }
                    }
                }
            }
            46 => {
                v___x_7885_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_7874_,
                    v___y_7878_,
                    v___y_7871_,
                    v___y_7879_,
                    v___y_7873_,
                );
                if lean_obj_tag(v___x_7885_) == 0 {
                    v_a_7886_ = lean_ctor_get(v___x_7885_, 0);
                    lean_inc(v_a_7886_);
                    lean_dec_ref_known(v___x_7885_, 1);
                    v___x_7887_ = l_Lean_LibrarySuggestions_select(
                        v_a_7886_,
                        v___y_7884_,
                        v___y_7878_,
                        v___y_7871_,
                        v___y_7879_,
                        v___y_7873_,
                    );
                    if lean_obj_tag(v___x_7887_) == 0 {
                        v_a_7888_ = lean_ctor_get(v___x_7887_, 0);
                        lean_inc(v_a_7888_);
                        lean_dec_ref_known(v___x_7887_, 1);
                        v_sz_7889_ = lean_array_size(v_a_7888_);
                        v___x_7890_ = 0usize;
                        v___x_7891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__1(v_a_7888_, v_sz_7889_, v___x_7890_, v___y_7882_, v___y_7876_, v___y_7874_, v___y_7881_, v___y_7877_, v___y_7878_, v___y_7871_, v___y_7879_, v___y_7873_);
                        lean_dec(v_a_7888_);
                        if lean_obj_tag(v___x_7891_) == 0 {
                            v_a_7892_ = lean_ctor_get(v___x_7891_, 0);
                            lean_inc(v_a_7892_);
                            lean_dec_ref_known(v___x_7891_, 1);
                            v___y_7837_ = v___y_7869_;
                            v___y_7838_ = v___y_7875_;
                            v___y_7839_ = v___y_7870_;
                            v___y_7840_ = v___y_7880_;
                            v___y_7841_ = v___y_7872_;
                            v___y_7842_ = v___y_7883_;
                            v_argsArray_7843_ = v_a_7892_;
                            v___y_7844_ = v___y_7876_;
                            v___y_7845_ = v___y_7874_;
                            v___y_7846_ = v___y_7881_;
                            v___y_7847_ = v___y_7877_;
                            v___y_7848_ = v___y_7878_;
                            v___y_7849_ = v___y_7871_;
                            v___y_7850_ = v___y_7879_;
                            v___y_7851_ = v___y_7873_;
                            state = 45;
                            continue;
                        } else {
                            lean_dec(v___y_7880_);
                            lean_dec(v___y_7875_);
                            lean_dec(v___y_7870_);
                            lean_dec(v___y_7869_);
                            lean_dec(v_tk_7032_);
                            lean_dec_ref(v___x_7019_);
                            lean_dec_ref(v___x_7018_);
                            lean_dec_ref(v___x_7017_);
                            v_a_7893_ = lean_ctor_get(v___x_7891_, 0);
                            v_isSharedCheck_7900_ = (!lean_is_exclusive(v___x_7891_)) as u8;
                            if v_isSharedCheck_7900_ == 0 {
                                v___x_7895_ = v___x_7891_;
                                v_isShared_7896_ = v_isSharedCheck_7900_;
                                state = 47;
                                continue;
                            } else {
                                lean_inc(v_a_7893_);
                                lean_dec(v___x_7891_);
                                v___x_7895_ = lean_box(0);
                                v_isShared_7896_ = v_isSharedCheck_7900_;
                                state = 47;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_7882_);
                        lean_dec(v___y_7880_);
                        lean_dec(v___y_7875_);
                        lean_dec(v___y_7870_);
                        lean_dec(v___y_7869_);
                        lean_dec(v_tk_7032_);
                        lean_dec_ref(v___x_7019_);
                        lean_dec_ref(v___x_7018_);
                        lean_dec_ref(v___x_7017_);
                        v_a_7901_ = lean_ctor_get(v___x_7887_, 0);
                        v_isSharedCheck_7908_ = (!lean_is_exclusive(v___x_7887_)) as u8;
                        if v_isSharedCheck_7908_ == 0 {
                            v___x_7903_ = v___x_7887_;
                            v_isShared_7904_ = v_isSharedCheck_7908_;
                            state = 49;
                            continue;
                        } else {
                            lean_inc(v_a_7901_);
                            lean_dec(v___x_7887_);
                            v___x_7903_ = lean_box(0);
                            v_isShared_7904_ = v_isSharedCheck_7908_;
                            state = 49;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7884_);
                    lean_dec_ref(v___y_7882_);
                    lean_dec(v___y_7880_);
                    lean_dec(v___y_7875_);
                    lean_dec(v___y_7870_);
                    lean_dec(v___y_7869_);
                    lean_dec(v_tk_7032_);
                    lean_dec_ref(v___x_7019_);
                    lean_dec_ref(v___x_7018_);
                    lean_dec_ref(v___x_7017_);
                    v_a_7909_ = lean_ctor_get(v___x_7885_, 0);
                    v_isSharedCheck_7916_ = (!lean_is_exclusive(v___x_7885_)) as u8;
                    if v_isSharedCheck_7916_ == 0 {
                        v___x_7911_ = v___x_7885_;
                        v_isShared_7912_ = v_isSharedCheck_7916_;
                        state = 51;
                        continue;
                    } else {
                        lean_inc(v_a_7909_);
                        lean_dec(v___x_7885_);
                        v___x_7911_ = lean_box(0);
                        v_isShared_7912_ = v_isSharedCheck_7916_;
                        state = 51;
                        continue;
                    }
                }
            }
            47 => {
                if v_isShared_7896_ == 0 {
                    v___x_7898_ = v___x_7895_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_7899_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7899_, 0, v_a_7893_);
                    v___x_7898_ = v_reuseFailAlloc_7899_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_7898_;
            }
            49 => {
                if v_isShared_7904_ == 0 {
                    v___x_7906_ = v___x_7903_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_7907_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7907_, 0, v_a_7901_);
                    v___x_7906_ = v_reuseFailAlloc_7907_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_7906_;
            }
            51 => {
                if v_isShared_7912_ == 0 {
                    v___x_7914_ = v___x_7911_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_7915_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7915_, 0, v_a_7909_);
                    v___x_7914_ = v_reuseFailAlloc_7915_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_7914_;
            }
            53 => {
                v_config_7934_ = lean_ctor_get(v___y_7925_, 0);
                lean_inc_ref(v_config_7934_);
                lean_dec_ref(v___y_7925_);
                v_suggestions_7935_ = lean_ctor_get_uint8(
                    v_config_7934_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 26) as u32,
                );
                if v_suggestions_7935_ == 0 {
                    lean_dec_ref(v_config_7934_);
                    lean_dec_ref(v___f_7020_);
                    v___y_7837_ = v___y_7918_;
                    v___y_7838_ = v___y_7924_;
                    v___y_7839_ = v___y_7919_;
                    v___y_7840_ = v___y_7930_;
                    v___y_7841_ = v___y_7921_;
                    v___y_7842_ = v___y_7932_;
                    v_argsArray_7843_ = v___y_7933_;
                    v___y_7844_ = v___y_7926_;
                    v___y_7845_ = v___y_7923_;
                    v___y_7846_ = v___y_7931_;
                    v___y_7847_ = v___y_7927_;
                    v___y_7848_ = v___y_7928_;
                    v___y_7849_ = v___y_7920_;
                    v___y_7850_ = v___y_7929_;
                    v___y_7851_ = v___y_7922_;
                    state = 45;
                    continue;
                } else {
                    v_maxSuggestions_7936_ = lean_ctor_get(v_config_7934_, 2);
                    lean_inc(v_maxSuggestions_7936_);
                    lean_dec_ref(v_config_7934_);
                    v___x_7937_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__11;
                    v___x_7938_ = lean_box(0);
                    if lean_obj_tag(v_maxSuggestions_7936_) == 0 {
                        v___x_7939_ = lean_unsigned_to_nat(100);
                        v___x_7940_ = lean_alloc_ctor(0, 4, (0) as u32);
                        lean_ctor_set(v___x_7940_, 0, v___x_7939_);
                        lean_ctor_set(v___x_7940_, 1, v___x_7937_);
                        lean_ctor_set(v___x_7940_, 2, v___f_7020_);
                        lean_ctor_set(v___x_7940_, 3, v___x_7938_);
                        v___y_7869_ = v___y_7918_;
                        v___y_7870_ = v___y_7919_;
                        v___y_7871_ = v___y_7920_;
                        v___y_7872_ = v___y_7921_;
                        v___y_7873_ = v___y_7922_;
                        v___y_7874_ = v___y_7923_;
                        v___y_7875_ = v___y_7924_;
                        v___y_7876_ = v___y_7926_;
                        v___y_7877_ = v___y_7927_;
                        v___y_7878_ = v___y_7928_;
                        v___y_7879_ = v___y_7929_;
                        v___y_7880_ = v___y_7930_;
                        v___y_7881_ = v___y_7931_;
                        v___y_7882_ = v___y_7933_;
                        v___y_7883_ = v___y_7932_;
                        v___y_7884_ = v___x_7940_;
                        state = 46;
                        continue;
                    } else {
                        v_val_7941_ = lean_ctor_get(v_maxSuggestions_7936_, 0);
                        lean_inc(v_val_7941_);
                        lean_dec_ref_known(v_maxSuggestions_7936_, 1);
                        v___x_7942_ = lean_alloc_ctor(0, 4, (0) as u32);
                        lean_ctor_set(v___x_7942_, 0, v_val_7941_);
                        lean_ctor_set(v___x_7942_, 1, v___x_7937_);
                        lean_ctor_set(v___x_7942_, 2, v___f_7020_);
                        lean_ctor_set(v___x_7942_, 3, v___x_7938_);
                        v___y_7869_ = v___y_7918_;
                        v___y_7870_ = v___y_7919_;
                        v___y_7871_ = v___y_7920_;
                        v___y_7872_ = v___y_7921_;
                        v___y_7873_ = v___y_7922_;
                        v___y_7874_ = v___y_7923_;
                        v___y_7875_ = v___y_7924_;
                        v___y_7876_ = v___y_7926_;
                        v___y_7877_ = v___y_7927_;
                        v___y_7878_ = v___y_7928_;
                        v___y_7879_ = v___y_7929_;
                        v___y_7880_ = v___y_7930_;
                        v___y_7881_ = v___y_7931_;
                        v___y_7882_ = v___y_7933_;
                        v___y_7883_ = v___y_7932_;
                        v___y_7884_ = v___x_7942_;
                        state = 46;
                        continue;
                    }
                }
            }
            54 => {
                v___x_7958_ = 1;
                lean_inc(v___y_7944_);
                v___x_7959_ = l_Lean_Elab_Tactic_elabSimpConfig___redArg(
                    v___y_7944_,
                    v___x_7958_,
                    v___y_7950_,
                    v___y_7952_,
                    v___y_7948_,
                );
                if lean_obj_tag(v___x_7959_) == 0 {
                    if lean_obj_tag(v___y_7946_) == 1 {
                        v_a_7960_ = lean_ctor_get(v___x_7959_, 0);
                        lean_inc(v_a_7960_);
                        lean_dec_ref_known(v___x_7959_, 1);
                        v_val_7961_ = lean_ctor_get(v___y_7946_, 0);
                        lean_inc(v_val_7961_);
                        lean_dec_ref_known(v___y_7946_, 1);
                        v___x_7962_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_7961_);
                        lean_dec(v_val_7961_);
                        v___y_7918_ = v___y_7944_;
                        v___y_7919_ = v___y_7945_;
                        v___y_7920_ = v___y_7947_;
                        v___y_7921_ = v___x_7958_;
                        v___y_7922_ = v___y_7948_;
                        v___y_7923_ = v___y_7949_;
                        v___y_7924_ = v___y_7957_;
                        v___y_7925_ = v_a_7960_;
                        v___y_7926_ = v___y_7950_;
                        v___y_7927_ = v___y_7951_;
                        v___y_7928_ = v___y_7953_;
                        v___y_7929_ = v___y_7952_;
                        v___y_7930_ = v___y_7954_;
                        v___y_7931_ = v___y_7955_;
                        v___y_7932_ = v___y_7956_;
                        v___y_7933_ = v___x_7962_;
                        state = 53;
                        continue;
                    } else {
                        lean_dec(v___y_7946_);
                        v_a_7963_ = lean_ctor_get(v___x_7959_, 0);
                        lean_inc(v_a_7963_);
                        lean_dec_ref_known(v___x_7959_, 1);
                        v___x_7964_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0;
                        v___y_7918_ = v___y_7944_;
                        v___y_7919_ = v___y_7945_;
                        v___y_7920_ = v___y_7947_;
                        v___y_7921_ = v___x_7958_;
                        v___y_7922_ = v___y_7948_;
                        v___y_7923_ = v___y_7949_;
                        v___y_7924_ = v___y_7957_;
                        v___y_7925_ = v_a_7963_;
                        v___y_7926_ = v___y_7950_;
                        v___y_7927_ = v___y_7951_;
                        v___y_7928_ = v___y_7953_;
                        v___y_7929_ = v___y_7952_;
                        v___y_7930_ = v___y_7954_;
                        v___y_7931_ = v___y_7955_;
                        v___y_7932_ = v___y_7956_;
                        v___y_7933_ = v___x_7964_;
                        state = 53;
                        continue;
                    }
                } else {
                    lean_dec(v___y_7957_);
                    lean_dec(v___y_7954_);
                    lean_dec(v___y_7946_);
                    lean_dec(v___y_7945_);
                    lean_dec(v___y_7944_);
                    lean_dec(v_tk_7032_);
                    lean_dec_ref(v___f_7020_);
                    lean_dec_ref(v___x_7019_);
                    lean_dec_ref(v___x_7018_);
                    lean_dec_ref(v___x_7017_);
                    v_a_7965_ = lean_ctor_get(v___x_7959_, 0);
                    v_isSharedCheck_7972_ = (!lean_is_exclusive(v___x_7959_)) as u8;
                    if v_isSharedCheck_7972_ == 0 {
                        v___x_7967_ = v___x_7959_;
                        v_isShared_7968_ = v_isSharedCheck_7972_;
                        state = 55;
                        continue;
                    } else {
                        lean_inc(v_a_7965_);
                        lean_dec(v___x_7959_);
                        v___x_7967_ = lean_box(0);
                        v_isShared_7968_ = v_isSharedCheck_7972_;
                        state = 55;
                        continue;
                    }
                }
            }
            55 => {
                if v_isShared_7968_ == 0 {
                    v___x_7970_ = v___x_7967_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_7971_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7971_, 0, v_a_7965_);
                    v___x_7970_ = v_reuseFailAlloc_7971_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_7970_;
            }
            57 => {
                v___x_7988_ = l_Lean_Syntax_getOptional_x3f(v___y_7975_);
                lean_dec(v___y_7975_);
                if lean_obj_tag(v___x_7988_) == 0 {
                    v___x_7989_ = lean_box(0);
                    v___y_7944_ = v___y_7974_;
                    v___y_7945_ = v___y_7976_;
                    v___y_7946_ = v_args_7979_;
                    v___y_7947_ = v___y_7985_;
                    v___y_7948_ = v___y_7987_;
                    v___y_7949_ = v___y_7981_;
                    v___y_7950_ = v___y_7980_;
                    v___y_7951_ = v___y_7983_;
                    v___y_7952_ = v___y_7986_;
                    v___y_7953_ = v___y_7984_;
                    v___y_7954_ = v___y_7977_;
                    v___y_7955_ = v___y_7982_;
                    v___y_7956_ = v___y_7978_;
                    v___y_7957_ = v___x_7989_;
                    state = 54;
                    continue;
                } else {
                    v_val_7990_ = lean_ctor_get(v___x_7988_, 0);
                    v_isSharedCheck_7997_ = (!lean_is_exclusive(v___x_7988_)) as u8;
                    if v_isSharedCheck_7997_ == 0 {
                        v___x_7992_ = v___x_7988_;
                        v_isShared_7993_ = v_isSharedCheck_7997_;
                        state = 58;
                        continue;
                    } else {
                        lean_inc(v_val_7990_);
                        lean_dec(v___x_7988_);
                        v___x_7992_ = lean_box(0);
                        v_isShared_7993_ = v_isSharedCheck_7997_;
                        state = 58;
                        continue;
                    }
                }
            }
            58 => {
                if v_isShared_7993_ == 0 {
                    v___x_7995_ = v___x_7992_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_7996_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7996_, 0, v_val_7990_);
                    v___x_7995_ = v_reuseFailAlloc_7996_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                v___y_7944_ = v___y_7974_;
                v___y_7945_ = v___y_7976_;
                v___y_7946_ = v_args_7979_;
                v___y_7947_ = v___y_7985_;
                v___y_7948_ = v___y_7987_;
                v___y_7949_ = v___y_7981_;
                v___y_7950_ = v___y_7980_;
                v___y_7951_ = v___y_7983_;
                v___y_7952_ = v___y_7986_;
                v___y_7953_ = v___y_7984_;
                v___y_7954_ = v___y_7977_;
                v___y_7955_ = v___y_7982_;
                v___y_7956_ = v___y_7978_;
                v___y_7957_ = v___x_7995_;
                state = 54;
                continue;
            }
            60 => {
                v___x_8014_ = lean_unsigned_to_nat(3);
                v___x_8015_ = l_Lean_Syntax_getArg(v___y_8000_, v___x_8014_);
                lean_dec(v___y_8000_);
                v___x_8016_ = l_Lean_Syntax_isNone(v___x_8015_);
                if v___x_8016_ == 0 {
                    lean_inc(v___x_8015_);
                    v___x_8017_ = l_Lean_Syntax_matchesNull(v___x_8015_, v___x_7998_);
                    if v___x_8017_ == 0 {
                        lean_dec(v___x_8015_);
                        lean_dec(v_o_8005_);
                        lean_dec(v___y_8003_);
                        lean_dec(v___y_8002_);
                        lean_dec(v___y_8001_);
                        lean_dec(v_tk_7032_);
                        lean_dec_ref(v___f_7020_);
                        lean_dec_ref(v___x_7019_);
                        lean_dec_ref(v___x_7018_);
                        lean_dec_ref(v___x_7017_);
                        v___x_8018_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                        return v___x_8018_;
                    } else {
                        v___x_8019_ = l_Lean_Syntax_getArg(v___x_8015_, v___x_7031_);
                        lean_dec(v___x_8015_);
                        v___x_8020_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12;
                        lean_inc_ref(v___x_7019_);
                        lean_inc_ref(v___x_7018_);
                        lean_inc_ref(v___x_7017_);
                        v___x_8021_ =
                            l_Lean_Name_mkStr4(v___x_7017_, v___x_7018_, v___x_7019_, v___x_8020_);
                        lean_inc(v___x_8019_);
                        v___x_8022_ = l_Lean_Syntax_isOfKind(v___x_8019_, v___x_8021_);
                        lean_dec(v___x_8021_);
                        if v___x_8022_ == 0 {
                            lean_dec(v___x_8019_);
                            lean_dec(v_o_8005_);
                            lean_dec(v___y_8003_);
                            lean_dec(v___y_8002_);
                            lean_dec(v___y_8001_);
                            lean_dec(v_tk_7032_);
                            lean_dec_ref(v___f_7020_);
                            lean_dec_ref(v___x_7019_);
                            lean_dec_ref(v___x_7018_);
                            lean_dec_ref(v___x_7017_);
                            v___x_8023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                            return v___x_8023_;
                        } else {
                            v___x_8024_ = l_Lean_Syntax_getArg(v___x_8019_, v___x_7998_);
                            lean_dec(v___x_8019_);
                            v_args_8025_ = l_Lean_Syntax_getArgs(v___x_8024_);
                            lean_dec(v___x_8024_);
                            v___x_8026_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_8026_, 0, v_args_8025_);
                            v___y_7974_ = v___y_8001_;
                            v___y_7975_ = v___y_8002_;
                            v___y_7976_ = v_o_8005_;
                            v___y_7977_ = v___y_8003_;
                            v___y_7978_ = v___y_8004_;
                            v_args_7979_ = v___x_8026_;
                            v___y_7980_ = v___y_8006_;
                            v___y_7981_ = v___y_8007_;
                            v___y_7982_ = v___y_8008_;
                            v___y_7983_ = v___y_8009_;
                            v___y_7984_ = v___y_8010_;
                            v___y_7985_ = v___y_8011_;
                            v___y_7986_ = v___y_8012_;
                            v___y_7987_ = v___y_8013_;
                            state = 57;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_8015_);
                    v___x_8027_ = lean_box(0);
                    v___y_7974_ = v___y_8001_;
                    v___y_7975_ = v___y_8002_;
                    v___y_7976_ = v_o_8005_;
                    v___y_7977_ = v___y_8003_;
                    v___y_7978_ = v___y_8004_;
                    v_args_7979_ = v___x_8027_;
                    v___y_7980_ = v___y_8006_;
                    v___y_7981_ = v___y_8007_;
                    v___y_7982_ = v___y_8008_;
                    v___y_7983_ = v___y_8009_;
                    v___y_7984_ = v___y_8010_;
                    v___y_7985_ = v___y_8011_;
                    v___y_7986_ = v___y_8012_;
                    v___y_7987_ = v___y_8013_;
                    state = 57;
                    continue;
                }
            }
            61 => {
                v___x_8038_ = lean_unsigned_to_nat(2);
                v___x_8039_ = l_Lean_Syntax_getArg(v_stx_7015_, v___x_8038_);
                v___x_8040_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__13;
                lean_inc_ref(v___x_7019_);
                lean_inc_ref(v___x_7018_);
                lean_inc_ref(v___x_7017_);
                v___x_8041_ =
                    l_Lean_Name_mkStr4(v___x_7017_, v___x_7018_, v___x_7019_, v___x_8040_);
                lean_inc(v___x_8039_);
                v___x_8042_ = l_Lean_Syntax_isOfKind(v___x_8039_, v___x_8041_);
                lean_dec(v___x_8041_);
                if v___x_8042_ == 0 {
                    lean_dec(v___x_8039_);
                    lean_dec(v_bang_8029_);
                    lean_dec(v_tk_7032_);
                    lean_dec_ref(v___f_7020_);
                    lean_dec_ref(v___x_7019_);
                    lean_dec_ref(v___x_7018_);
                    lean_dec_ref(v___x_7017_);
                    v___x_8043_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                    return v___x_8043_;
                } else {
                    v_cfg_8044_ = l_Lean_Syntax_getArg(v___x_8039_, v___x_7031_);
                    v___x_8045_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15;
                    lean_inc_ref(v___x_7019_);
                    lean_inc_ref(v___x_7018_);
                    lean_inc_ref(v___x_7017_);
                    v___x_8046_ =
                        l_Lean_Name_mkStr4(v___x_7017_, v___x_7018_, v___x_7019_, v___x_8045_);
                    lean_inc(v_cfg_8044_);
                    v___x_8047_ = l_Lean_Syntax_isOfKind(v_cfg_8044_, v___x_8046_);
                    lean_dec(v___x_8046_);
                    if v___x_8047_ == 0 {
                        lean_dec(v_cfg_8044_);
                        lean_dec(v___x_8039_);
                        lean_dec(v_bang_8029_);
                        lean_dec(v_tk_7032_);
                        lean_dec_ref(v___f_7020_);
                        lean_dec_ref(v___x_7019_);
                        lean_dec_ref(v___x_7018_);
                        lean_dec_ref(v___x_7017_);
                        v___x_8048_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                        return v___x_8048_;
                    } else {
                        v___x_8049_ = l_Lean_Syntax_getArg(v___x_8039_, v___x_7998_);
                        v___x_8050_ = l_Lean_Syntax_getArg(v___x_8039_, v___x_8038_);
                        v___x_8051_ = l_Lean_Syntax_isNone(v___x_8050_);
                        if v___x_8051_ == 0 {
                            lean_inc(v___x_8050_);
                            v___x_8052_ = l_Lean_Syntax_matchesNull(v___x_8050_, v___x_7998_);
                            if v___x_8052_ == 0 {
                                lean_dec(v___x_8050_);
                                lean_dec(v___x_8049_);
                                lean_dec(v_cfg_8044_);
                                lean_dec(v___x_8039_);
                                lean_dec(v_bang_8029_);
                                lean_dec(v_tk_7032_);
                                lean_dec_ref(v___f_7020_);
                                lean_dec_ref(v___x_7019_);
                                lean_dec_ref(v___x_7018_);
                                lean_dec_ref(v___x_7017_);
                                v___x_8053_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                                return v___x_8053_;
                            } else {
                                v_o_8054_ = l_Lean_Syntax_getArg(v___x_8050_, v___x_7031_);
                                lean_dec(v___x_8050_);
                                v___x_8055_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_8055_, 0, v_o_8054_);
                                v___y_8000_ = v___x_8039_;
                                v___y_8001_ = v_cfg_8044_;
                                v___y_8002_ = v___x_8049_;
                                v___y_8003_ = v_bang_8029_;
                                v___y_8004_ = v___x_8047_;
                                v_o_8005_ = v___x_8055_;
                                v___y_8006_ = v___y_8030_;
                                v___y_8007_ = v___y_8031_;
                                v___y_8008_ = v___y_8032_;
                                v___y_8009_ = v___y_8033_;
                                v___y_8010_ = v___y_8034_;
                                v___y_8011_ = v___y_8035_;
                                v___y_8012_ = v___y_8036_;
                                v___y_8013_ = v___y_8037_;
                                state = 60;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_8050_);
                            v___x_8056_ = lean_box(0);
                            v___y_8000_ = v___x_8039_;
                            v___y_8001_ = v_cfg_8044_;
                            v___y_8002_ = v___x_8049_;
                            v___y_8003_ = v_bang_8029_;
                            v___y_8004_ = v___x_8047_;
                            v_o_8005_ = v___x_8056_;
                            v___y_8006_ = v___y_8030_;
                            v___y_8007_ = v___y_8031_;
                            v___y_8008_ = v___y_8032_;
                            v___y_8009_ = v___y_8033_;
                            v___y_8010_ = v___y_8034_;
                            v___y_8011_ = v___y_8035_;
                            v___y_8012_ = v___y_8036_;
                            v___y_8013_ = v___y_8037_;
                            state = 60;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed(
    mut v___x_8064_: *mut LeanObject,
    mut v_stx_8065_: *mut LeanObject,
    mut v___x_8066_: *mut LeanObject,
    mut v___x_8067_: *mut LeanObject,
    mut v___x_8068_: *mut LeanObject,
    mut v___x_8069_: *mut LeanObject,
    mut v___f_8070_: *mut LeanObject,
    mut v___y_8071_: *mut LeanObject,
    mut v___y_8072_: *mut LeanObject,
    mut v___y_8073_: *mut LeanObject,
    mut v___y_8074_: *mut LeanObject,
    mut v___y_8075_: *mut LeanObject,
    mut v___y_8076_: *mut LeanObject,
    mut v___y_8077_: *mut LeanObject,
    mut v___y_8078_: *mut LeanObject,
    mut v___y_8079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_39049__boxed_8080_: u8 = 0;
    let mut v___x_39050__boxed_8081_: u8 = 0;
    let mut v_res_8082_: *mut LeanObject = core::ptr::null_mut();
    v___x_39049__boxed_8080_ = (lean_unbox(v___x_8064_) as u8);
    v___x_39050__boxed_8081_ = (lean_unbox(v___x_8066_) as u8);
    v_res_8082_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1(
        v___x_39049__boxed_8080_,
        v_stx_8065_,
        v___x_39050__boxed_8081_,
        v___x_8067_,
        v___x_8068_,
        v___x_8069_,
        v___f_8070_,
        v___y_8071_,
        v___y_8072_,
        v___y_8073_,
        v___y_8074_,
        v___y_8075_,
        v___y_8076_,
        v___y_8077_,
        v___y_8078_,
    );
    lean_dec(v___y_8078_);
    lean_dec_ref(v___y_8077_);
    lean_dec(v___y_8076_);
    lean_dec_ref(v___y_8075_);
    lean_dec(v___y_8074_);
    lean_dec_ref(v___y_8073_);
    lean_dec(v___y_8072_);
    lean_dec_ref(v___y_8071_);
    lean_dec(v_stx_8065_);
    return v_res_8082_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpAllTrace(
    mut v_stx_8089_: *mut LeanObject,
    mut v_a_8090_: *mut LeanObject,
    mut v_a_8091_: *mut LeanObject,
    mut v_a_8092_: *mut LeanObject,
    mut v_a_8093_: *mut LeanObject,
    mut v_a_8094_: *mut LeanObject,
    mut v_a_8095_: *mut LeanObject,
    mut v_a_8096_: *mut LeanObject,
    mut v_a_8097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8103_: u8 = 0;
    let mut v___x_8104_: u8 = 0;
    let mut v___f_8105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8110_: *mut LeanObject = core::ptr::null_mut();
    v___x_8099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0;
    v___x_8100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1;
    v___x_8101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2;
    v___x_8102_ = l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1;
    lean_inc(v_stx_8089_);
    v___x_8103_ = l_Lean_Syntax_isOfKind(v_stx_8089_, v___x_8102_);
    v___x_8104_ = 1;
    v___f_8105_ = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
    v___x_8106_ = lean_box((v___x_8103_) as usize);
    v___x_8107_ = lean_box((v___x_8104_) as usize);
    v___y_8108_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___boxed as *mut core::ffi::c_void,
        16,
        7,
    );
    lean_closure_set(v___y_8108_, 0, v___x_8106_);
    lean_closure_set(v___y_8108_, 1, v_stx_8089_);
    lean_closure_set(v___y_8108_, 2, v___x_8107_);
    lean_closure_set(v___y_8108_, 3, v___x_8099_);
    lean_closure_set(v___y_8108_, 4, v___x_8100_);
    lean_closure_set(v___y_8108_, 5, v___x_8101_);
    lean_closure_set(v___y_8108_, 6, v___f_8105_);
    v___x_8109_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_withSimpDiagnostics___boxed as *mut core::ffi::c_void,
        10,
        1,
    );
    lean_closure_set(v___x_8109_, 0, v___y_8108_);
    v___x_8110_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___x_8109_,
        v_a_8090_,
        v_a_8091_,
        v_a_8092_,
        v_a_8093_,
        v_a_8094_,
        v_a_8095_,
        v_a_8096_,
        v_a_8097_,
    );
    return v___x_8110_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(
    mut v_stx_8111_: *mut LeanObject,
    mut v_a_8112_: *mut LeanObject,
    mut v_a_8113_: *mut LeanObject,
    mut v_a_8114_: *mut LeanObject,
    mut v_a_8115_: *mut LeanObject,
    mut v_a_8116_: *mut LeanObject,
    mut v_a_8117_: *mut LeanObject,
    mut v_a_8118_: *mut LeanObject,
    mut v_a_8119_: *mut LeanObject,
    mut v_a_8120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8121_: *mut LeanObject = core::ptr::null_mut();
    v_res_8121_ = l_Lean_Elab_Tactic_evalSimpAllTrace(
        v_stx_8111_,
        v_a_8112_,
        v_a_8113_,
        v_a_8114_,
        v_a_8115_,
        v_a_8116_,
        v_a_8117_,
        v_a_8118_,
        v_a_8119_,
    );
    lean_dec(v_a_8119_);
    lean_dec_ref(v_a_8118_);
    lean_dec(v_a_8117_);
    lean_dec_ref(v_a_8116_);
    lean_dec(v_a_8115_);
    lean_dec_ref(v_a_8114_);
    lean_dec(v_a_8113_);
    lean_dec_ref(v_a_8112_);
    return v_res_8121_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(
    mut v___x_8122_: *mut LeanObject,
    mut v_as_8123_: *mut LeanObject,
    mut v_as_x27_8124_: *mut LeanObject,
    mut v_b_8125_: *mut LeanObject,
    mut v_a_8126_: *mut LeanObject,
    mut v___y_8127_: *mut LeanObject,
    mut v___y_8128_: *mut LeanObject,
    mut v___y_8129_: *mut LeanObject,
    mut v___y_8130_: *mut LeanObject,
    mut v___y_8131_: *mut LeanObject,
    mut v___y_8132_: *mut LeanObject,
    mut v___y_8133_: *mut LeanObject,
    mut v___y_8134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8136_: *mut LeanObject = core::ptr::null_mut();
    v___x_8136_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___redArg(
        v___x_8122_,
        v_as_x27_8124_,
        v_b_8125_,
        v___y_8133_,
    );
    return v___x_8136_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0___boxed(
    mut v___x_8137_: *mut LeanObject,
    mut v_as_8138_: *mut LeanObject,
    mut v_as_x27_8139_: *mut LeanObject,
    mut v_b_8140_: *mut LeanObject,
    mut v_a_8141_: *mut LeanObject,
    mut v___y_8142_: *mut LeanObject,
    mut v___y_8143_: *mut LeanObject,
    mut v___y_8144_: *mut LeanObject,
    mut v___y_8145_: *mut LeanObject,
    mut v___y_8146_: *mut LeanObject,
    mut v___y_8147_: *mut LeanObject,
    mut v___y_8148_: *mut LeanObject,
    mut v___y_8149_: *mut LeanObject,
    mut v___y_8150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8151_: *mut LeanObject = core::ptr::null_mut();
    v_res_8151_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpAllTrace_spec__0(
        v___x_8137_,
        v_as_8138_,
        v_as_x27_8139_,
        v_b_8140_,
        v_a_8141_,
        v___y_8142_,
        v___y_8143_,
        v___y_8144_,
        v___y_8145_,
        v___y_8146_,
        v___y_8147_,
        v___y_8148_,
        v___y_8149_,
    );
    lean_dec(v___y_8149_);
    lean_dec_ref(v___y_8148_);
    lean_dec(v___y_8147_);
    lean_dec_ref(v___y_8146_);
    lean_dec(v___y_8145_);
    lean_dec_ref(v___y_8144_);
    lean_dec(v___y_8143_);
    lean_dec_ref(v___y_8142_);
    lean_dec(v_as_x27_8139_);
    lean_dec(v_as_8138_);
    lean_dec(v___x_8137_);
    return v_res_8151_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1()
-> *mut LeanObject {
    let mut v___x_8159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8163_: *mut LeanObject = core::ptr::null_mut();
    v___x_8159_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_8160_ = l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1;
    v___x_8161_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1;
    v___x_8162_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSimpAllTrace___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_8163_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_8159_,
        v___x_8160_,
        v___x_8161_,
        v___x_8162_,
    );
    return v___x_8163_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___boxed(
    mut v_a_8164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8165_: *mut LeanObject = core::ptr::null_mut();
    v_res_8165_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
    return v_res_8165_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3()
-> *mut LeanObject {
    let mut v___x_8191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8193_: *mut LeanObject = core::ptr::null_mut();
    v___x_8191_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1;
    v___x_8192_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6;
    v___x_8193_ = l_Lean_addBuiltinDeclarationRanges(v___x_8191_, v___x_8192_);
    return v___x_8193_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___boxed(
    mut v_a_8194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8195_: *mut LeanObject = core::ptr::null_mut();
    v_res_8195_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
    return v_res_8195_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(
    mut v_ctx_8196_: *mut LeanObject,
    mut v_simprocs_8197_: *mut LeanObject,
    mut v_fvarIdsToSimp_8198_: *mut LeanObject,
    mut v_simplifyTarget_8199_: u8,
    mut v_a_8200_: *mut LeanObject,
    mut v_a_8201_: *mut LeanObject,
    mut v_a_8202_: *mut LeanObject,
    mut v_a_8203_: *mut LeanObject,
    mut v_a_8204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8219_: u8 = 0;
    let mut v___x_8221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8223_: u8 = 0;
    let mut v_unused_8224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8228_: u8 = 0;
    let mut v___x_8230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8232_: u8 = 0;
    let mut v_snd_8233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8236_: u8 = 0;
    let mut v_val_8237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8244_: u8 = 0;
    let mut v___x_8246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8248_: u8 = 0;
    let mut v_unused_8249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8253_: u8 = 0;
    let mut v___x_8255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8257_: u8 = 0;
    let mut v_reuseFailAlloc_8258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8259_: u8 = 0;
    let mut v_unused_8260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8264_: u8 = 0;
    let mut v___x_8266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8268_: u8 = 0;
    let mut v_a_8269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8272_: u8 = 0;
    let mut v___x_8274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8206_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_8200_, v_a_8201_, v_a_8202_, v_a_8203_, v_a_8204_,
                );
                if lean_obj_tag(v___x_8206_) == 0 {
                    v_a_8207_ = lean_ctor_get(v___x_8206_, 0);
                    lean_inc(v_a_8207_);
                    lean_dec_ref_known(v___x_8206_, 1);
                    v___x_8208_ = lean_unsigned_to_nat(32);
                    v___x_8209_ = lean_mk_empty_array_with_capacity(v___x_8208_);
                    lean_dec_ref(v___x_8209_);
                    v___x_8210_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6_once
                        ),
                        _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__6,
                    );
                    v___x_8211_ = l_Lean_Meta_dsimpGoal(
                        v_a_8207_,
                        v_ctx_8196_,
                        v_simprocs_8197_,
                        v_simplifyTarget_8199_,
                        v_fvarIdsToSimp_8198_,
                        v___x_8210_,
                        v_a_8201_,
                        v_a_8202_,
                        v_a_8203_,
                        v_a_8204_,
                    );
                    if lean_obj_tag(v___x_8211_) == 0 {
                        v_a_8212_ = lean_ctor_get(v___x_8211_, 0);
                        lean_inc(v_a_8212_);
                        lean_dec_ref_known(v___x_8211_, 1);
                        v_fst_8213_ = lean_ctor_get(v_a_8212_, 0);
                        if lean_obj_tag(v_fst_8213_) == 0 {
                            v_snd_8214_ = lean_ctor_get(v_a_8212_, 1);
                            lean_inc(v_snd_8214_);
                            lean_dec(v_a_8212_);
                            v___x_8215_ = lean_box(0);
                            v___x_8216_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v___x_8215_,
                                v_a_8200_,
                                v_a_8201_,
                                v_a_8202_,
                                v_a_8203_,
                                v_a_8204_,
                            );
                            if lean_obj_tag(v___x_8216_) == 0 {
                                v_isSharedCheck_8223_ = (!lean_is_exclusive(v___x_8216_)) as u8;
                                if v_isSharedCheck_8223_ == 0 {
                                    v_unused_8224_ = lean_ctor_get(v___x_8216_, 0);
                                    lean_dec(v_unused_8224_);
                                    v___x_8218_ = v___x_8216_;
                                    v_isShared_8219_ = v_isSharedCheck_8223_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___x_8216_);
                                    v___x_8218_ = lean_box(0);
                                    v_isShared_8219_ = v_isSharedCheck_8223_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_snd_8214_);
                                v_a_8225_ = lean_ctor_get(v___x_8216_, 0);
                                v_isSharedCheck_8232_ = (!lean_is_exclusive(v___x_8216_)) as u8;
                                if v_isSharedCheck_8232_ == 0 {
                                    v___x_8227_ = v___x_8216_;
                                    v_isShared_8228_ = v_isSharedCheck_8232_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_8225_);
                                    lean_dec(v___x_8216_);
                                    v___x_8227_ = lean_box(0);
                                    v_isShared_8228_ = v_isSharedCheck_8232_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc_ref(v_fst_8213_);
                            v_snd_8233_ = lean_ctor_get(v_a_8212_, 1);
                            v_isSharedCheck_8259_ = (!lean_is_exclusive(v_a_8212_)) as u8;
                            if v_isSharedCheck_8259_ == 0 {
                                v_unused_8260_ = lean_ctor_get(v_a_8212_, 0);
                                lean_dec(v_unused_8260_);
                                v___x_8235_ = v_a_8212_;
                                v_isShared_8236_ = v_isSharedCheck_8259_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_snd_8233_);
                                lean_dec(v_a_8212_);
                                v___x_8235_ = lean_box(0);
                                v_isShared_8236_ = v_isSharedCheck_8259_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_8261_ = lean_ctor_get(v___x_8211_, 0);
                        v_isSharedCheck_8268_ = (!lean_is_exclusive(v___x_8211_)) as u8;
                        if v_isSharedCheck_8268_ == 0 {
                            v___x_8263_ = v___x_8211_;
                            v_isShared_8264_ = v_isSharedCheck_8268_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_8261_);
                            lean_dec(v___x_8211_);
                            v___x_8263_ = lean_box(0);
                            v_isShared_8264_ = v_isSharedCheck_8268_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_fvarIdsToSimp_8198_);
                    lean_dec_ref(v_simprocs_8197_);
                    lean_dec_ref(v_ctx_8196_);
                    v_a_8269_ = lean_ctor_get(v___x_8206_, 0);
                    v_isSharedCheck_8276_ = (!lean_is_exclusive(v___x_8206_)) as u8;
                    if v_isSharedCheck_8276_ == 0 {
                        v___x_8271_ = v___x_8206_;
                        v_isShared_8272_ = v_isSharedCheck_8276_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_8269_);
                        lean_dec(v___x_8206_);
                        v___x_8271_ = lean_box(0);
                        v_isShared_8272_ = v_isSharedCheck_8276_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8219_ == 0 {
                    lean_ctor_set(v___x_8218_, 0, v_snd_8214_);
                    v___x_8221_ = v___x_8218_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8222_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8222_, 0, v_snd_8214_);
                    v___x_8221_ = v_reuseFailAlloc_8222_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8221_;
            }
            3 => {
                if v_isShared_8228_ == 0 {
                    v___x_8230_ = v___x_8227_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8231_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8231_, 0, v_a_8225_);
                    v___x_8230_ = v_reuseFailAlloc_8231_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8230_;
            }
            5 => {
                v_val_8237_ = lean_ctor_get(v_fst_8213_, 0);
                lean_inc(v_val_8237_);
                lean_dec_ref_known(v_fst_8213_, 1);
                v___x_8238_ = lean_box(0);
                if v_isShared_8236_ == 0 {
                    lean_ctor_set_tag(v___x_8235_, 1);
                    lean_ctor_set(v___x_8235_, 1, v___x_8238_);
                    lean_ctor_set(v___x_8235_, 0, v_val_8237_);
                    v___x_8240_ = v___x_8235_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8258_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8258_, 0, v_val_8237_);
                    lean_ctor_set(v_reuseFailAlloc_8258_, 1, v___x_8238_);
                    v___x_8240_ = v_reuseFailAlloc_8258_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_8241_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_8240_,
                    v_a_8200_,
                    v_a_8201_,
                    v_a_8202_,
                    v_a_8203_,
                    v_a_8204_,
                );
                if lean_obj_tag(v___x_8241_) == 0 {
                    v_isSharedCheck_8248_ = (!lean_is_exclusive(v___x_8241_)) as u8;
                    if v_isSharedCheck_8248_ == 0 {
                        v_unused_8249_ = lean_ctor_get(v___x_8241_, 0);
                        lean_dec(v_unused_8249_);
                        v___x_8243_ = v___x_8241_;
                        v_isShared_8244_ = v_isSharedCheck_8248_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_8241_);
                        v___x_8243_ = lean_box(0);
                        v_isShared_8244_ = v_isSharedCheck_8248_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_8233_);
                    v_a_8250_ = lean_ctor_get(v___x_8241_, 0);
                    v_isSharedCheck_8257_ = (!lean_is_exclusive(v___x_8241_)) as u8;
                    if v_isSharedCheck_8257_ == 0 {
                        v___x_8252_ = v___x_8241_;
                        v_isShared_8253_ = v_isSharedCheck_8257_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_8250_);
                        lean_dec(v___x_8241_);
                        v___x_8252_ = lean_box(0);
                        v_isShared_8253_ = v_isSharedCheck_8257_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_8244_ == 0 {
                    lean_ctor_set(v___x_8243_, 0, v_snd_8233_);
                    v___x_8246_ = v___x_8243_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8247_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8247_, 0, v_snd_8233_);
                    v___x_8246_ = v_reuseFailAlloc_8247_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8246_;
            }
            9 => {
                if v_isShared_8253_ == 0 {
                    v___x_8255_ = v___x_8252_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8256_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8256_, 0, v_a_8250_);
                    v___x_8255_ = v_reuseFailAlloc_8256_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8255_;
            }
            11 => {
                if v_isShared_8264_ == 0 {
                    v___x_8266_ = v___x_8263_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_8267_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8267_, 0, v_a_8261_);
                    v___x_8266_ = v_reuseFailAlloc_8267_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_8266_;
            }
            13 => {
                if v_isShared_8272_ == 0 {
                    v___x_8274_ = v___x_8271_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_8275_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8275_, 0, v_a_8269_);
                    v___x_8274_ = v_reuseFailAlloc_8275_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_8274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(
    mut v_ctx_8277_: *mut LeanObject,
    mut v_simprocs_8278_: *mut LeanObject,
    mut v_fvarIdsToSimp_8279_: *mut LeanObject,
    mut v_simplifyTarget_8280_: *mut LeanObject,
    mut v_a_8281_: *mut LeanObject,
    mut v_a_8282_: *mut LeanObject,
    mut v_a_8283_: *mut LeanObject,
    mut v_a_8284_: *mut LeanObject,
    mut v_a_8285_: *mut LeanObject,
    mut v_a_8286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_simplifyTarget_boxed_8287_: u8 = 0;
    let mut v_res_8288_: *mut LeanObject = core::ptr::null_mut();
    v_simplifyTarget_boxed_8287_ = (lean_unbox(v_simplifyTarget_8280_) as u8);
    v_res_8288_ =
        l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(
            v_ctx_8277_,
            v_simprocs_8278_,
            v_fvarIdsToSimp_8279_,
            v_simplifyTarget_boxed_8287_,
            v_a_8281_,
            v_a_8282_,
            v_a_8283_,
            v_a_8284_,
            v_a_8285_,
        );
    lean_dec(v_a_8285_);
    lean_dec_ref(v_a_8284_);
    lean_dec(v_a_8283_);
    lean_dec_ref(v_a_8282_);
    lean_dec(v_a_8281_);
    return v_res_8288_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(
    mut v_ctx_8289_: *mut LeanObject,
    mut v_simprocs_8290_: *mut LeanObject,
    mut v_fvarIdsToSimp_8291_: *mut LeanObject,
    mut v_simplifyTarget_8292_: u8,
    mut v_a_8293_: *mut LeanObject,
    mut v_a_8294_: *mut LeanObject,
    mut v_a_8295_: *mut LeanObject,
    mut v_a_8296_: *mut LeanObject,
    mut v_a_8297_: *mut LeanObject,
    mut v_a_8298_: *mut LeanObject,
    mut v_a_8299_: *mut LeanObject,
    mut v_a_8300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8302_: *mut LeanObject = core::ptr::null_mut();
    v___x_8302_ =
        l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(
            v_ctx_8289_,
            v_simprocs_8290_,
            v_fvarIdsToSimp_8291_,
            v_simplifyTarget_8292_,
            v_a_8294_,
            v_a_8297_,
            v_a_8298_,
            v_a_8299_,
            v_a_8300_,
        );
    return v___x_8302_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(
    mut v_ctx_8303_: *mut LeanObject,
    mut v_simprocs_8304_: *mut LeanObject,
    mut v_fvarIdsToSimp_8305_: *mut LeanObject,
    mut v_simplifyTarget_8306_: *mut LeanObject,
    mut v_a_8307_: *mut LeanObject,
    mut v_a_8308_: *mut LeanObject,
    mut v_a_8309_: *mut LeanObject,
    mut v_a_8310_: *mut LeanObject,
    mut v_a_8311_: *mut LeanObject,
    mut v_a_8312_: *mut LeanObject,
    mut v_a_8313_: *mut LeanObject,
    mut v_a_8314_: *mut LeanObject,
    mut v_a_8315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_simplifyTarget_boxed_8316_: u8 = 0;
    let mut v_res_8317_: *mut LeanObject = core::ptr::null_mut();
    v_simplifyTarget_boxed_8316_ = (lean_unbox(v_simplifyTarget_8306_) as u8);
    v_res_8317_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(
        v_ctx_8303_,
        v_simprocs_8304_,
        v_fvarIdsToSimp_8305_,
        v_simplifyTarget_boxed_8316_,
        v_a_8307_,
        v_a_8308_,
        v_a_8309_,
        v_a_8310_,
        v_a_8311_,
        v_a_8312_,
        v_a_8313_,
        v_a_8314_,
    );
    lean_dec(v_a_8314_);
    lean_dec_ref(v_a_8313_);
    lean_dec(v_a_8312_);
    lean_dec_ref(v_a_8311_);
    lean_dec(v_a_8310_);
    lean_dec_ref(v_a_8309_);
    lean_dec(v_a_8308_);
    lean_dec_ref(v_a_8307_);
    return v_res_8317_;
}
pub unsafe fn l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(
    mut v_ctx_8318_: *mut LeanObject,
    mut v_simprocs_8319_: *mut LeanObject,
    mut v___y_8320_: *mut LeanObject,
    mut v___y_8321_: *mut LeanObject,
    mut v___y_8322_: *mut LeanObject,
    mut v___y_8323_: *mut LeanObject,
    mut v___y_8324_: *mut LeanObject,
    mut v___y_8325_: *mut LeanObject,
    mut v___y_8326_: *mut LeanObject,
    mut v___y_8327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8333_: u8 = 0;
    let mut v___x_8334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8338_: u8 = 0;
    let mut v___x_8340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8342_: u8 = 0;
    let mut v_a_8343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8346_: u8 = 0;
    let mut v___x_8348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8329_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_8321_,
                    v___y_8324_,
                    v___y_8325_,
                    v___y_8326_,
                    v___y_8327_,
                );
                if lean_obj_tag(v___x_8329_) == 0 {
                    v_a_8330_ = lean_ctor_get(v___x_8329_, 0);
                    lean_inc(v_a_8330_);
                    lean_dec_ref_known(v___x_8329_, 1);
                    v___x_8331_ = l_Lean_MVarId_getNondepPropHyps(
                        v_a_8330_,
                        v___y_8324_,
                        v___y_8325_,
                        v___y_8326_,
                        v___y_8327_,
                    );
                    if lean_obj_tag(v___x_8331_) == 0 {
                        v_a_8332_ = lean_ctor_get(v___x_8331_, 0);
                        lean_inc(v_a_8332_);
                        lean_dec_ref_known(v___x_8331_, 1);
                        v___x_8333_ = 1;
                        v___x_8334_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_8318_, v_simprocs_8319_, v_a_8332_, v___x_8333_, v___y_8321_, v___y_8324_, v___y_8325_, v___y_8326_, v___y_8327_);
                        return v___x_8334_;
                    } else {
                        lean_dec_ref(v_simprocs_8319_);
                        lean_dec_ref(v_ctx_8318_);
                        v_a_8335_ = lean_ctor_get(v___x_8331_, 0);
                        v_isSharedCheck_8342_ = (!lean_is_exclusive(v___x_8331_)) as u8;
                        if v_isSharedCheck_8342_ == 0 {
                            v___x_8337_ = v___x_8331_;
                            v_isShared_8338_ = v_isSharedCheck_8342_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8335_);
                            lean_dec(v___x_8331_);
                            v___x_8337_ = lean_box(0);
                            v_isShared_8338_ = v_isSharedCheck_8342_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_simprocs_8319_);
                    lean_dec_ref(v_ctx_8318_);
                    v_a_8343_ = lean_ctor_get(v___x_8329_, 0);
                    v_isSharedCheck_8350_ = (!lean_is_exclusive(v___x_8329_)) as u8;
                    if v_isSharedCheck_8350_ == 0 {
                        v___x_8345_ = v___x_8329_;
                        v_isShared_8346_ = v_isSharedCheck_8350_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8343_);
                        lean_dec(v___x_8329_);
                        v___x_8345_ = lean_box(0);
                        v_isShared_8346_ = v_isSharedCheck_8350_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8338_ == 0 {
                    v___x_8340_ = v___x_8337_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8341_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8341_, 0, v_a_8335_);
                    v___x_8340_ = v_reuseFailAlloc_8341_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8340_;
            }
            3 => {
                if v_isShared_8346_ == 0 {
                    v___x_8348_ = v___x_8345_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8349_, 0, v_a_8343_);
                    v___x_8348_ = v_reuseFailAlloc_8349_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(
    mut v_ctx_8351_: *mut LeanObject,
    mut v_simprocs_8352_: *mut LeanObject,
    mut v___y_8353_: *mut LeanObject,
    mut v___y_8354_: *mut LeanObject,
    mut v___y_8355_: *mut LeanObject,
    mut v___y_8356_: *mut LeanObject,
    mut v___y_8357_: *mut LeanObject,
    mut v___y_8358_: *mut LeanObject,
    mut v___y_8359_: *mut LeanObject,
    mut v___y_8360_: *mut LeanObject,
    mut v___y_8361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8362_: *mut LeanObject = core::ptr::null_mut();
    v_res_8362_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(
        v_ctx_8351_,
        v_simprocs_8352_,
        v___y_8353_,
        v___y_8354_,
        v___y_8355_,
        v___y_8356_,
        v___y_8357_,
        v___y_8358_,
        v___y_8359_,
        v___y_8360_,
    );
    lean_dec(v___y_8360_);
    lean_dec_ref(v___y_8359_);
    lean_dec(v___y_8358_);
    lean_dec_ref(v___y_8357_);
    lean_dec(v___y_8356_);
    lean_dec_ref(v___y_8355_);
    lean_dec(v___y_8354_);
    lean_dec_ref(v___y_8353_);
    return v_res_8362_;
}
pub unsafe fn l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(
    mut v_hypotheses_8363_: *mut LeanObject,
    mut v_ctx_8364_: *mut LeanObject,
    mut v_simprocs_8365_: *mut LeanObject,
    mut v_type_8366_: u8,
    mut v___y_8367_: *mut LeanObject,
    mut v___y_8368_: *mut LeanObject,
    mut v___y_8369_: *mut LeanObject,
    mut v___y_8370_: *mut LeanObject,
    mut v___y_8371_: *mut LeanObject,
    mut v___y_8372_: *mut LeanObject,
    mut v___y_8373_: *mut LeanObject,
    mut v___y_8374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8382_: u8 = 0;
    let mut v___x_8384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8376_ = l_Lean_Elab_Tactic_getFVarIds(
                    v_hypotheses_8363_,
                    v___y_8367_,
                    v___y_8368_,
                    v___y_8369_,
                    v___y_8370_,
                    v___y_8371_,
                    v___y_8372_,
                    v___y_8373_,
                    v___y_8374_,
                );
                if lean_obj_tag(v___x_8376_) == 0 {
                    v_a_8377_ = lean_ctor_get(v___x_8376_, 0);
                    lean_inc(v_a_8377_);
                    lean_dec_ref_known(v___x_8376_, 1);
                    v___x_8378_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(v_ctx_8364_, v_simprocs_8365_, v_a_8377_, v_type_8366_, v___y_8368_, v___y_8371_, v___y_8372_, v___y_8373_, v___y_8374_);
                    return v___x_8378_;
                } else {
                    lean_dec_ref(v_simprocs_8365_);
                    lean_dec_ref(v_ctx_8364_);
                    v_a_8379_ = lean_ctor_get(v___x_8376_, 0);
                    v_isSharedCheck_8386_ = (!lean_is_exclusive(v___x_8376_)) as u8;
                    if v_isSharedCheck_8386_ == 0 {
                        v___x_8381_ = v___x_8376_;
                        v_isShared_8382_ = v_isSharedCheck_8386_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8379_);
                        lean_dec(v___x_8376_);
                        v___x_8381_ = lean_box(0);
                        v_isShared_8382_ = v_isSharedCheck_8386_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8382_ == 0 {
                    v___x_8384_ = v___x_8381_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8385_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8385_, 0, v_a_8379_);
                    v___x_8384_ = v_reuseFailAlloc_8385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8384_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(
    mut v_hypotheses_8387_: *mut LeanObject,
    mut v_ctx_8388_: *mut LeanObject,
    mut v_simprocs_8389_: *mut LeanObject,
    mut v_type_8390_: *mut LeanObject,
    mut v___y_8391_: *mut LeanObject,
    mut v___y_8392_: *mut LeanObject,
    mut v___y_8393_: *mut LeanObject,
    mut v___y_8394_: *mut LeanObject,
    mut v___y_8395_: *mut LeanObject,
    mut v___y_8396_: *mut LeanObject,
    mut v___y_8397_: *mut LeanObject,
    mut v___y_8398_: *mut LeanObject,
    mut v___y_8399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_635__boxed_8400_: u8 = 0;
    let mut v_res_8401_: *mut LeanObject = core::ptr::null_mut();
    v_type_635__boxed_8400_ = (lean_unbox(v_type_8390_) as u8);
    v_res_8401_ = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(
        v_hypotheses_8387_,
        v_ctx_8388_,
        v_simprocs_8389_,
        v_type_635__boxed_8400_,
        v___y_8391_,
        v___y_8392_,
        v___y_8393_,
        v___y_8394_,
        v___y_8395_,
        v___y_8396_,
        v___y_8397_,
        v___y_8398_,
    );
    lean_dec(v___y_8398_);
    lean_dec_ref(v___y_8397_);
    lean_dec(v___y_8396_);
    lean_dec_ref(v___y_8395_);
    lean_dec(v___y_8394_);
    lean_dec_ref(v___y_8393_);
    lean_dec(v___y_8392_);
    lean_dec_ref(v___y_8391_);
    return v_res_8401_;
}
pub unsafe fn l_Lean_Elab_Tactic_dsimpLocation_x27(
    mut v_ctx_8402_: *mut LeanObject,
    mut v_simprocs_8403_: *mut LeanObject,
    mut v_loc_8404_: *mut LeanObject,
    mut v_a_8405_: *mut LeanObject,
    mut v_a_8406_: *mut LeanObject,
    mut v_a_8407_: *mut LeanObject,
    mut v_a_8408_: *mut LeanObject,
    mut v_a_8409_: *mut LeanObject,
    mut v_a_8410_: *mut LeanObject,
    mut v_a_8411_: *mut LeanObject,
    mut v_a_8412_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_loc_8404_) == 0 {
        let mut v___f_8414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8415_: *mut LeanObject = core::ptr::null_mut();
        v___f_8414_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed as *mut core::ffi::c_void,
            11,
            2,
        );
        lean_closure_set(v___f_8414_, 0, v_ctx_8402_);
        lean_closure_set(v___f_8414_, 1, v_simprocs_8403_);
        v___x_8415_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_8414_,
            v_a_8405_,
            v_a_8406_,
            v_a_8407_,
            v_a_8408_,
            v_a_8409_,
            v_a_8410_,
            v_a_8411_,
            v_a_8412_,
        );
        return v___x_8415_;
    } else {
        let mut v_hypotheses_8416_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_8417_: u8 = 0;
        let mut v___x_8418_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_8419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8420_: *mut LeanObject = core::ptr::null_mut();
        v_hypotheses_8416_ = lean_ctor_get(v_loc_8404_, 0);
        lean_inc_ref(v_hypotheses_8416_);
        v_type_8417_ = lean_ctor_get_uint8(
            v_loc_8404_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        );
        lean_dec_ref_known(v_loc_8404_, 1);
        v___x_8418_ = lean_box((v_type_8417_) as usize);
        v___f_8419_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed as *mut core::ffi::c_void,
            13,
            4,
        );
        lean_closure_set(v___f_8419_, 0, v_hypotheses_8416_);
        lean_closure_set(v___f_8419_, 1, v_ctx_8402_);
        lean_closure_set(v___f_8419_, 2, v_simprocs_8403_);
        lean_closure_set(v___f_8419_, 3, v___x_8418_);
        v___x_8420_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_8419_,
            v_a_8405_,
            v_a_8406_,
            v_a_8407_,
            v_a_8408_,
            v_a_8409_,
            v_a_8410_,
            v_a_8411_,
            v_a_8412_,
        );
        return v___x_8420_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(
    mut v_ctx_8421_: *mut LeanObject,
    mut v_simprocs_8422_: *mut LeanObject,
    mut v_loc_8423_: *mut LeanObject,
    mut v_a_8424_: *mut LeanObject,
    mut v_a_8425_: *mut LeanObject,
    mut v_a_8426_: *mut LeanObject,
    mut v_a_8427_: *mut LeanObject,
    mut v_a_8428_: *mut LeanObject,
    mut v_a_8429_: *mut LeanObject,
    mut v_a_8430_: *mut LeanObject,
    mut v_a_8431_: *mut LeanObject,
    mut v_a_8432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8433_: *mut LeanObject = core::ptr::null_mut();
    v_res_8433_ = l_Lean_Elab_Tactic_dsimpLocation_x27(
        v_ctx_8421_,
        v_simprocs_8422_,
        v_loc_8423_,
        v_a_8424_,
        v_a_8425_,
        v_a_8426_,
        v_a_8427_,
        v_a_8428_,
        v_a_8429_,
        v_a_8430_,
        v_a_8431_,
    );
    lean_dec(v_a_8431_);
    lean_dec_ref(v_a_8430_);
    lean_dec(v_a_8429_);
    lean_dec_ref(v_a_8428_);
    lean_dec(v_a_8427_);
    lean_dec_ref(v_a_8426_);
    lean_dec(v_a_8425_);
    lean_dec_ref(v_a_8424_);
    return v_res_8433_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(
    mut v___x_8438_: u8,
    mut v_stx_8439_: *mut LeanObject,
    mut v___x_8440_: u8,
    mut v___x_8441_: *mut LeanObject,
    mut v___x_8442_: *mut LeanObject,
    mut v___x_8443_: *mut LeanObject,
    mut v___y_8444_: *mut LeanObject,
    mut v___y_8445_: *mut LeanObject,
    mut v___y_8446_: *mut LeanObject,
    mut v___y_8447_: *mut LeanObject,
    mut v___y_8448_: *mut LeanObject,
    mut v___y_8449_: *mut LeanObject,
    mut v___y_8450_: *mut LeanObject,
    mut v___y_8451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_8455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_8471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_8472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8475_: u8 = 0;
    let mut v___x_8476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8486_: u8 = 0;
    let mut v___x_8487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8491_: u8 = 0;
    let mut v___x_8493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8495_: u8 = 0;
    let mut v_unused_8496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8500_: u8 = 0;
    let mut v___x_8502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8504_: u8 = 0;
    let mut v_reuseFailAlloc_8505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8509_: u8 = 0;
    let mut v___x_8511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8513_: u8 = 0;
    let mut v_isSharedCheck_8514_: u8 = 0;
    let mut v_a_8515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8518_: u8 = 0;
    let mut v___x_8520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8522_: u8 = 0;
    let mut v___y_8524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8543_: u8 = 0;
    let mut v_stx_8544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8553_: u8 = 0;
    let mut v___x_8554_: u8 = 0;
    let mut v___x_8555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_8562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocs_8563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_8564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocs_8565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_8566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocs_8567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8572_: u8 = 0;
    let mut v___x_8574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8576_: u8 = 0;
    let mut v___y_8578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8587_: u8 = 0;
    let mut v___y_8588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8611_: u8 = 0;
    let mut v___y_8612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8638_: u8 = 0;
    let mut v___y_8639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8669_: u8 = 0;
    let mut v___y_8670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8694_: u8 = 0;
    let mut v___y_8695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8721_: u8 = 0;
    let mut v___y_8722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8752_: u8 = 0;
    let mut v___y_8753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8760_: u8 = 0;
    let mut v_ref_8761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8783_: u8 = 0;
    let mut v___y_8784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8791_: u8 = 0;
    let mut v_ref_8792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8793_: u8 = 0;
    let mut v___x_8794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8811_: u8 = 0;
    let mut v___y_8812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_8815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8831_: u8 = 0;
    let mut v___x_8833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8835_: u8 = 0;
    let mut v___x_8836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8840_: u8 = 0;
    let mut v___y_8841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_o_8843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8853_: u8 = 0;
    let mut v___x_8854_: u8 = 0;
    let mut v___x_8855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8859_: u8 = 0;
    let mut v___x_8860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_8862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bang_8866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8879_: u8 = 0;
    let mut v___x_8880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8884_: u8 = 0;
    let mut v___x_8885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8887_: u8 = 0;
    let mut v___x_8888_: u8 = 0;
    let mut v___x_8889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_o_8890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8894_: u8 = 0;
    let mut v___x_8895_: u8 = 0;
    let mut v___x_8896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bang_8897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8899_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_8438_ == 0 {
                    lean_dec_ref(v___x_8443_);
                    lean_dec_ref(v___x_8442_);
                    lean_dec_ref(v___x_8441_);
                    v___x_8453_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                    return v___x_8453_;
                } else {
                    v___x_8454_ = lean_unsigned_to_nat(0);
                    v_tk_8455_ = l_Lean_Syntax_getArg(v_stx_8439_, v___x_8454_);
                    v___x_8836_ = lean_unsigned_to_nat(1);
                    v___x_8893_ = l_Lean_Syntax_getArg(v_stx_8439_, v___x_8836_);
                    v___x_8894_ = l_Lean_Syntax_isNone(v___x_8893_);
                    if v___x_8894_ == 0 {
                        lean_inc(v___x_8893_);
                        v___x_8895_ = l_Lean_Syntax_matchesNull(v___x_8893_, v___x_8836_);
                        if v___x_8895_ == 0 {
                            lean_dec(v___x_8893_);
                            lean_dec(v_tk_8455_);
                            lean_dec_ref(v___x_8443_);
                            lean_dec_ref(v___x_8442_);
                            lean_dec_ref(v___x_8441_);
                            v___x_8896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                            return v___x_8896_;
                        } else {
                            v_bang_8897_ = l_Lean_Syntax_getArg(v___x_8893_, v___x_8454_);
                            lean_dec(v___x_8893_);
                            v___x_8898_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_8898_, 0, v_bang_8897_);
                            v_bang_8866_ = v___x_8898_;
                            v___y_8867_ = v___y_8444_;
                            v___y_8868_ = v___y_8445_;
                            v___y_8869_ = v___y_8446_;
                            v___y_8870_ = v___y_8447_;
                            v___y_8871_ = v___y_8448_;
                            v___y_8872_ = v___y_8449_;
                            v___y_8873_ = v___y_8450_;
                            v___y_8874_ = v___y_8451_;
                            state = 28;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_8893_);
                        v___x_8899_ = lean_box(0);
                        v_bang_8866_ = v___x_8899_;
                        v___y_8867_ = v___y_8444_;
                        v___y_8868_ = v___y_8445_;
                        v___y_8869_ = v___y_8446_;
                        v___y_8870_ = v___y_8447_;
                        v___y_8871_ = v___y_8448_;
                        v___y_8872_ = v___y_8449_;
                        v___y_8873_ = v___y_8450_;
                        v___y_8874_ = v___y_8451_;
                        state = 28;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8469_ = l_Lean_Elab_Tactic_dsimpLocation_x27(
                    v___y_8465_,
                    v___y_8458_,
                    v___y_8468_,
                    v___y_8466_,
                    v___y_8467_,
                    v___y_8462_,
                    v___y_8457_,
                    v___y_8464_,
                    v___y_8461_,
                    v___y_8463_,
                    v___y_8459_,
                );
                if lean_obj_tag(v___x_8469_) == 0 {
                    v_a_8470_ = lean_ctor_get(v___x_8469_, 0);
                    lean_inc(v_a_8470_);
                    lean_dec_ref_known(v___x_8469_, 1);
                    v_usedTheorems_8471_ = lean_ctor_get(v_a_8470_, 0);
                    v_diag_8472_ = lean_ctor_get(v_a_8470_, 1);
                    v_isSharedCheck_8514_ = (!lean_is_exclusive(v_a_8470_)) as u8;
                    if v_isSharedCheck_8514_ == 0 {
                        v___x_8474_ = v_a_8470_;
                        v_isShared_8475_ = v_isSharedCheck_8514_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_diag_8472_);
                        lean_inc(v_usedTheorems_8471_);
                        lean_dec(v_a_8470_);
                        v___x_8474_ = lean_box(0);
                        v_isShared_8475_ = v_isSharedCheck_8514_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___y_8460_);
                    lean_dec(v_tk_8455_);
                    v_a_8515_ = lean_ctor_get(v___x_8469_, 0);
                    v_isSharedCheck_8522_ = (!lean_is_exclusive(v___x_8469_)) as u8;
                    if v_isSharedCheck_8522_ == 0 {
                        v___x_8517_ = v___x_8469_;
                        v_isShared_8518_ = v_isSharedCheck_8522_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_8515_);
                        lean_dec(v___x_8469_);
                        v___x_8517_ = lean_box(0);
                        v_isShared_8518_ = v_isSharedCheck_8522_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8476_ = l_Lean_Elab_Tactic_mkSimpCallStx(
                    v___y_8460_,
                    v_usedTheorems_8471_,
                    v___y_8464_,
                    v___y_8461_,
                    v___y_8463_,
                    v___y_8459_,
                );
                lean_dec_ref(v_usedTheorems_8471_);
                if lean_obj_tag(v___x_8476_) == 0 {
                    v_a_8477_ = lean_ctor_get(v___x_8476_, 0);
                    lean_inc(v_a_8477_);
                    lean_dec_ref_known(v___x_8476_, 1);
                    v_ref_8478_ = lean_ctor_get(v___y_8463_, 5);
                    v___x_8479_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
                    if v_isShared_8475_ == 0 {
                        lean_ctor_set(v___x_8474_, 1, v_a_8477_);
                        lean_ctor_set(v___x_8474_, 0, v___x_8479_);
                        v___x_8481_ = v___x_8474_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8505_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8505_, 0, v___x_8479_);
                        lean_ctor_set(v_reuseFailAlloc_8505_, 1, v_a_8477_);
                        v___x_8481_ = v_reuseFailAlloc_8505_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8474_);
                    lean_dec_ref(v_diag_8472_);
                    lean_dec(v_tk_8455_);
                    v_a_8506_ = lean_ctor_get(v___x_8476_, 0);
                    v_isSharedCheck_8513_ = (!lean_is_exclusive(v___x_8476_)) as u8;
                    if v_isSharedCheck_8513_ == 0 {
                        v___x_8508_ = v___x_8476_;
                        v_isShared_8509_ = v_isSharedCheck_8513_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_8506_);
                        lean_dec(v___x_8476_);
                        v___x_8508_ = lean_box(0);
                        v_isShared_8509_ = v_isSharedCheck_8513_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_8482_ = lean_box(0);
                v___x_8483_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_8483_, 0, v___x_8481_);
                lean_ctor_set(v___x_8483_, 1, v___x_8482_);
                lean_ctor_set(v___x_8483_, 2, v___x_8482_);
                lean_ctor_set(v___x_8483_, 3, v___x_8482_);
                lean_ctor_set(v___x_8483_, 4, v___x_8482_);
                lean_ctor_set(v___x_8483_, 5, v___x_8482_);
                lean_inc(v_ref_8478_);
                v___x_8484_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_8484_, 0, v_ref_8478_);
                v___x_8485_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
                v___x_8486_ = 4;
                v___x_8487_ = l_Lean_MessageData_nil;
                v___x_8488_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_tk_8455_,
                    v___x_8483_,
                    v___x_8484_,
                    v___x_8485_,
                    v___x_8482_,
                    v___x_8486_,
                    v___x_8487_,
                    v___y_8463_,
                    v___y_8459_,
                );
                if lean_obj_tag(v___x_8488_) == 0 {
                    v_isSharedCheck_8495_ = (!lean_is_exclusive(v___x_8488_)) as u8;
                    if v_isSharedCheck_8495_ == 0 {
                        v_unused_8496_ = lean_ctor_get(v___x_8488_, 0);
                        lean_dec(v_unused_8496_);
                        v___x_8490_ = v___x_8488_;
                        v_isShared_8491_ = v_isSharedCheck_8495_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_8488_);
                        v___x_8490_ = lean_box(0);
                        v_isShared_8491_ = v_isSharedCheck_8495_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_diag_8472_);
                    v_a_8497_ = lean_ctor_get(v___x_8488_, 0);
                    v_isSharedCheck_8504_ = (!lean_is_exclusive(v___x_8488_)) as u8;
                    if v_isSharedCheck_8504_ == 0 {
                        v___x_8499_ = v___x_8488_;
                        v_isShared_8500_ = v_isSharedCheck_8504_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8497_);
                        lean_dec(v___x_8488_);
                        v___x_8499_ = lean_box(0);
                        v_isShared_8500_ = v_isSharedCheck_8504_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_8491_ == 0 {
                    lean_ctor_set(v___x_8490_, 0, v_diag_8472_);
                    v___x_8493_ = v___x_8490_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8494_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8494_, 0, v_diag_8472_);
                    v___x_8493_ = v_reuseFailAlloc_8494_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8493_;
            }
            6 => {
                if v_isShared_8500_ == 0 {
                    v___x_8502_ = v___x_8499_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8503_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8503_, 0, v_a_8497_);
                    v___x_8502_ = v_reuseFailAlloc_8503_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8502_;
            }
            8 => {
                if v_isShared_8509_ == 0 {
                    v___x_8511_ = v___x_8508_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8512_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8512_, 0, v_a_8506_);
                    v___x_8511_ = v_reuseFailAlloc_8512_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8511_;
            }
            10 => {
                if v_isShared_8518_ == 0 {
                    v___x_8520_ = v___x_8517_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8521_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8521_, 0, v_a_8515_);
                    v___x_8520_ = v_reuseFailAlloc_8521_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8520_;
            }
            12 => {
                if lean_obj_tag(v___y_8527_) == 0 {
                    v___x_8536_ = l_Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig___redArg___closed__0;
                    v___x_8537_ = lean_alloc_ctor(1, 1, (1) as u32);
                    lean_ctor_set(v___x_8537_, 0, v___x_8536_);
                    lean_ctor_set_uint8(
                        v___x_8537_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_8440_,
                    );
                    v___y_8457_ = v___y_8524_;
                    v___y_8458_ = v___y_8525_;
                    v___y_8459_ = v___y_8526_;
                    v___y_8460_ = v___y_8530_;
                    v___y_8461_ = v___y_8529_;
                    v___y_8462_ = v___y_8528_;
                    v___y_8463_ = v___y_8531_;
                    v___y_8464_ = v___y_8532_;
                    v___y_8465_ = v___y_8535_;
                    v___y_8466_ = v___y_8533_;
                    v___y_8467_ = v___y_8534_;
                    v___y_8468_ = v___x_8537_;
                    state = 1;
                    continue;
                } else {
                    v_val_8538_ = lean_ctor_get(v___y_8527_, 0);
                    lean_inc(v_val_8538_);
                    lean_dec_ref_known(v___y_8527_, 1);
                    v___x_8539_ = l_Lean_Elab_Tactic_expandLocation(v_val_8538_);
                    lean_dec(v_val_8538_);
                    v___y_8457_ = v___y_8524_;
                    v___y_8458_ = v___y_8525_;
                    v___y_8459_ = v___y_8526_;
                    v___y_8460_ = v___y_8530_;
                    v___y_8461_ = v___y_8529_;
                    v___y_8462_ = v___y_8528_;
                    v___y_8463_ = v___y_8531_;
                    v___y_8464_ = v___y_8532_;
                    v___y_8465_ = v___y_8535_;
                    v___y_8466_ = v___y_8533_;
                    v___y_8467_ = v___y_8534_;
                    v___y_8468_ = v___x_8539_;
                    state = 1;
                    continue;
                }
            }
            13 => {
                v___x_8553_ = 0;
                v___x_8554_ = 2;
                v___x_8555_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3;
                v___x_8556_ = lean_box((v___x_8553_) as usize);
                v___x_8557_ = lean_box((v___x_8554_) as usize);
                v___x_8558_ = lean_box((v___x_8553_) as usize);
                lean_inc(v_stx_8544_);
                v___x_8559_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_mkSimpContext___boxed as *mut core::ffi::c_void,
                    14,
                    5,
                );
                lean_closure_set(v___x_8559_, 0, v_stx_8544_);
                lean_closure_set(v___x_8559_, 1, v___x_8556_);
                lean_closure_set(v___x_8559_, 2, v___x_8557_);
                lean_closure_set(v___x_8559_, 3, v___x_8558_);
                lean_closure_set(v___x_8559_, 4, v___x_8555_);
                v___x_8560_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___x_8559_,
                    v___y_8545_,
                    v___y_8546_,
                    v___y_8547_,
                    v___y_8548_,
                    v___y_8549_,
                    v___y_8550_,
                    v___y_8551_,
                    v___y_8552_,
                );
                if lean_obj_tag(v___x_8560_) == 0 {
                    v_a_8561_ = lean_ctor_get(v___x_8560_, 0);
                    lean_inc(v_a_8561_);
                    lean_dec_ref_known(v___x_8560_, 1);
                    if lean_obj_tag(v___y_8541_) == 0 {
                        v_ctx_8562_ = lean_ctor_get(v_a_8561_, 0);
                        lean_inc_ref(v_ctx_8562_);
                        v_simprocs_8563_ = lean_ctor_get(v_a_8561_, 1);
                        lean_inc_ref(v_simprocs_8563_);
                        lean_dec(v_a_8561_);
                        v___y_8524_ = v___y_8548_;
                        v___y_8525_ = v_simprocs_8563_;
                        v___y_8526_ = v___y_8552_;
                        v___y_8527_ = v___y_8542_;
                        v___y_8528_ = v___y_8547_;
                        v___y_8529_ = v___y_8550_;
                        v___y_8530_ = v_stx_8544_;
                        v___y_8531_ = v___y_8551_;
                        v___y_8532_ = v___y_8549_;
                        v___y_8533_ = v___y_8545_;
                        v___y_8534_ = v___y_8546_;
                        v___y_8535_ = v_ctx_8562_;
                        state = 12;
                        continue;
                    } else {
                        lean_dec_ref_known(v___y_8541_, 1);
                        if v___y_8543_ == 0 {
                            v_ctx_8564_ = lean_ctor_get(v_a_8561_, 0);
                            lean_inc_ref(v_ctx_8564_);
                            v_simprocs_8565_ = lean_ctor_get(v_a_8561_, 1);
                            lean_inc_ref(v_simprocs_8565_);
                            lean_dec(v_a_8561_);
                            v___y_8524_ = v___y_8548_;
                            v___y_8525_ = v_simprocs_8565_;
                            v___y_8526_ = v___y_8552_;
                            v___y_8527_ = v___y_8542_;
                            v___y_8528_ = v___y_8547_;
                            v___y_8529_ = v___y_8550_;
                            v___y_8530_ = v_stx_8544_;
                            v___y_8531_ = v___y_8551_;
                            v___y_8532_ = v___y_8549_;
                            v___y_8533_ = v___y_8545_;
                            v___y_8534_ = v___y_8546_;
                            v___y_8535_ = v_ctx_8564_;
                            state = 12;
                            continue;
                        } else {
                            v_ctx_8566_ = lean_ctor_get(v_a_8561_, 0);
                            lean_inc_ref(v_ctx_8566_);
                            v_simprocs_8567_ = lean_ctor_get(v_a_8561_, 1);
                            lean_inc_ref(v_simprocs_8567_);
                            lean_dec(v_a_8561_);
                            v___x_8568_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_8566_);
                            v___y_8524_ = v___y_8548_;
                            v___y_8525_ = v_simprocs_8567_;
                            v___y_8526_ = v___y_8552_;
                            v___y_8527_ = v___y_8542_;
                            v___y_8528_ = v___y_8547_;
                            v___y_8529_ = v___y_8550_;
                            v___y_8530_ = v_stx_8544_;
                            v___y_8531_ = v___y_8551_;
                            v___y_8532_ = v___y_8549_;
                            v___y_8533_ = v___y_8545_;
                            v___y_8534_ = v___y_8546_;
                            v___y_8535_ = v___x_8568_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_stx_8544_);
                    lean_dec(v___y_8542_);
                    lean_dec(v___y_8541_);
                    lean_dec(v_tk_8455_);
                    v_a_8569_ = lean_ctor_get(v___x_8560_, 0);
                    v_isSharedCheck_8576_ = (!lean_is_exclusive(v___x_8560_)) as u8;
                    if v_isSharedCheck_8576_ == 0 {
                        v___x_8571_ = v___x_8560_;
                        v_isShared_8572_ = v_isSharedCheck_8576_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_8569_);
                        lean_dec(v___x_8560_);
                        v___x_8571_ = lean_box(0);
                        v_isShared_8572_ = v_isSharedCheck_8576_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_8572_ == 0 {
                    v___x_8574_ = v___x_8571_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_8575_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8575_, 0, v_a_8569_);
                    v___x_8574_ = v_reuseFailAlloc_8575_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_8574_;
            }
            16 => {
                lean_inc_ref(v___y_8596_);
                v___x_8599_ = l_Array_append___redArg(v___y_8596_, v___y_8598_);
                lean_dec_ref(v___y_8598_);
                lean_inc(v___y_8582_);
                lean_inc(v___y_8595_);
                v___x_8600_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_8600_, 0, v___y_8595_);
                lean_ctor_set(v___x_8600_, 1, v___y_8582_);
                lean_ctor_set(v___x_8600_, 2, v___x_8599_);
                v___x_8601_ = l_Lean_Syntax_node6(
                    v___y_8595_,
                    v___y_8584_,
                    v___y_8593_,
                    v___y_8597_,
                    v___y_8592_,
                    v___y_8585_,
                    v___y_8586_,
                    v___x_8600_,
                );
                v___y_8541_ = v___y_8583_;
                v___y_8542_ = v___y_8594_;
                v___y_8543_ = v___y_8587_;
                v_stx_8544_ = v___x_8601_;
                v___y_8545_ = v___y_8579_;
                v___y_8546_ = v___y_8580_;
                v___y_8547_ = v___y_8590_;
                v___y_8548_ = v___y_8581_;
                v___y_8549_ = v___y_8588_;
                v___y_8550_ = v___y_8589_;
                v___y_8551_ = v___y_8591_;
                v___y_8552_ = v___y_8578_;
                state = 13;
                continue;
            }
            17 => {
                lean_inc_ref(v___y_8620_);
                v___x_8623_ = l_Array_append___redArg(v___y_8620_, v___y_8622_);
                lean_dec_ref(v___y_8622_);
                lean_inc(v___y_8607_);
                lean_inc(v___y_8619_);
                v___x_8624_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_8624_, 0, v___y_8619_);
                lean_ctor_set(v___x_8624_, 1, v___y_8607_);
                lean_ctor_set(v___x_8624_, 2, v___x_8623_);
                if lean_obj_tag(v___y_8618_) == 0 {
                    v___x_8625_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_8578_ = v___y_8603_;
                    v___y_8579_ = v___y_8604_;
                    v___y_8580_ = v___y_8605_;
                    v___y_8581_ = v___y_8606_;
                    v___y_8582_ = v___y_8607_;
                    v___y_8583_ = v___y_8608_;
                    v___y_8584_ = v___y_8609_;
                    v___y_8585_ = v___y_8610_;
                    v___y_8586_ = v___x_8624_;
                    v___y_8587_ = v___y_8611_;
                    v___y_8588_ = v___y_8612_;
                    v___y_8589_ = v___y_8614_;
                    v___y_8590_ = v___y_8613_;
                    v___y_8591_ = v___y_8616_;
                    v___y_8592_ = v___y_8615_;
                    v___y_8593_ = v___y_8617_;
                    v___y_8594_ = v___y_8618_;
                    v___y_8595_ = v___y_8619_;
                    v___y_8596_ = v___y_8620_;
                    v___y_8597_ = v___y_8621_;
                    v___y_8598_ = v___x_8625_;
                    state = 16;
                    continue;
                } else {
                    v_val_8626_ = lean_ctor_get(v___y_8618_, 0);
                    v___x_8627_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    lean_inc(v_val_8626_);
                    v___x_8628_ = lean_array_push(v___x_8627_, v_val_8626_);
                    v___y_8578_ = v___y_8603_;
                    v___y_8579_ = v___y_8604_;
                    v___y_8580_ = v___y_8605_;
                    v___y_8581_ = v___y_8606_;
                    v___y_8582_ = v___y_8607_;
                    v___y_8583_ = v___y_8608_;
                    v___y_8584_ = v___y_8609_;
                    v___y_8585_ = v___y_8610_;
                    v___y_8586_ = v___x_8624_;
                    v___y_8587_ = v___y_8611_;
                    v___y_8588_ = v___y_8612_;
                    v___y_8589_ = v___y_8614_;
                    v___y_8590_ = v___y_8613_;
                    v___y_8591_ = v___y_8616_;
                    v___y_8592_ = v___y_8615_;
                    v___y_8593_ = v___y_8617_;
                    v___y_8594_ = v___y_8618_;
                    v___y_8595_ = v___y_8619_;
                    v___y_8596_ = v___y_8620_;
                    v___y_8597_ = v___y_8621_;
                    v___y_8598_ = v___x_8628_;
                    state = 16;
                    continue;
                }
            }
            18 => {
                lean_inc_ref(v___y_8647_);
                v___x_8650_ = l_Array_append___redArg(v___y_8647_, v___y_8649_);
                lean_dec_ref(v___y_8649_);
                lean_inc(v___y_8634_);
                lean_inc(v___y_8646_);
                v___x_8651_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_8651_, 0, v___y_8646_);
                lean_ctor_set(v___x_8651_, 1, v___y_8634_);
                lean_ctor_set(v___x_8651_, 2, v___x_8650_);
                if lean_obj_tag(v___y_8637_) == 1 {
                    v_val_8652_ = lean_ctor_get(v___y_8637_, 0);
                    lean_inc(v_val_8652_);
                    lean_dec_ref_known(v___y_8637_, 1);
                    v___x_8653_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
                    lean_inc_n(v___y_8646_, 3);
                    v___x_8654_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_8654_, 0, v___y_8646_);
                    lean_ctor_set(v___x_8654_, 1, v___x_8653_);
                    lean_inc_ref(v___y_8647_);
                    v___x_8655_ = l_Array_append___redArg(v___y_8647_, v_val_8652_);
                    lean_dec(v_val_8652_);
                    lean_inc(v___y_8634_);
                    v___x_8656_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_8656_, 0, v___y_8646_);
                    lean_ctor_set(v___x_8656_, 1, v___y_8634_);
                    lean_ctor_set(v___x_8656_, 2, v___x_8655_);
                    v___x_8657_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
                    v___x_8658_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_8658_, 0, v___y_8646_);
                    lean_ctor_set(v___x_8658_, 1, v___x_8657_);
                    v___x_8659_ = l_Array_mkArray3___redArg(v___x_8654_, v___x_8656_, v___x_8658_);
                    v___y_8603_ = v___y_8630_;
                    v___y_8604_ = v___y_8631_;
                    v___y_8605_ = v___y_8632_;
                    v___y_8606_ = v___y_8633_;
                    v___y_8607_ = v___y_8634_;
                    v___y_8608_ = v___y_8635_;
                    v___y_8609_ = v___y_8636_;
                    v___y_8610_ = v___x_8651_;
                    v___y_8611_ = v___y_8638_;
                    v___y_8612_ = v___y_8639_;
                    v___y_8613_ = v___y_8641_;
                    v___y_8614_ = v___y_8640_;
                    v___y_8615_ = v___y_8643_;
                    v___y_8616_ = v___y_8642_;
                    v___y_8617_ = v___y_8644_;
                    v___y_8618_ = v___y_8645_;
                    v___y_8619_ = v___y_8646_;
                    v___y_8620_ = v___y_8647_;
                    v___y_8621_ = v___y_8648_;
                    v___y_8622_ = v___x_8659_;
                    state = 17;
                    continue;
                } else {
                    lean_dec(v___y_8637_);
                    v___x_8660_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_8603_ = v___y_8630_;
                    v___y_8604_ = v___y_8631_;
                    v___y_8605_ = v___y_8632_;
                    v___y_8606_ = v___y_8633_;
                    v___y_8607_ = v___y_8634_;
                    v___y_8608_ = v___y_8635_;
                    v___y_8609_ = v___y_8636_;
                    v___y_8610_ = v___x_8651_;
                    v___y_8611_ = v___y_8638_;
                    v___y_8612_ = v___y_8639_;
                    v___y_8613_ = v___y_8641_;
                    v___y_8614_ = v___y_8640_;
                    v___y_8615_ = v___y_8643_;
                    v___y_8616_ = v___y_8642_;
                    v___y_8617_ = v___y_8644_;
                    v___y_8618_ = v___y_8645_;
                    v___y_8619_ = v___y_8646_;
                    v___y_8620_ = v___y_8647_;
                    v___y_8621_ = v___y_8648_;
                    v___y_8622_ = v___x_8660_;
                    state = 17;
                    continue;
                }
            }
            19 => {
                lean_inc_ref(v___y_8679_);
                v___x_8683_ = l_Array_append___redArg(v___y_8679_, v___y_8682_);
                lean_dec_ref(v___y_8682_);
                lean_inc(v___y_8672_);
                lean_inc(v___y_8668_);
                v___x_8684_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_8684_, 0, v___y_8668_);
                lean_ctor_set(v___x_8684_, 1, v___y_8672_);
                lean_ctor_set(v___x_8684_, 2, v___x_8683_);
                v___x_8685_ = l_Lean_Syntax_node6(
                    v___y_8668_,
                    v___y_8680_,
                    v___y_8676_,
                    v___y_8681_,
                    v___y_8677_,
                    v___y_8667_,
                    v___y_8670_,
                    v___x_8684_,
                );
                v___y_8541_ = v___y_8666_;
                v___y_8542_ = v___y_8678_;
                v___y_8543_ = v___y_8669_;
                v_stx_8544_ = v___x_8685_;
                v___y_8545_ = v___y_8663_;
                v___y_8546_ = v___y_8664_;
                v___y_8547_ = v___y_8674_;
                v___y_8548_ = v___y_8665_;
                v___y_8549_ = v___y_8671_;
                v___y_8550_ = v___y_8673_;
                v___y_8551_ = v___y_8675_;
                v___y_8552_ = v___y_8662_;
                state = 13;
                continue;
            }
            20 => {
                lean_inc_ref(v___y_8703_);
                v___x_8707_ = l_Array_append___redArg(v___y_8703_, v___y_8706_);
                lean_dec_ref(v___y_8706_);
                lean_inc(v___y_8695_);
                lean_inc(v___y_8693_);
                v___x_8708_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_8708_, 0, v___y_8693_);
                lean_ctor_set(v___x_8708_, 1, v___y_8695_);
                lean_ctor_set(v___x_8708_, 2, v___x_8707_);
                if lean_obj_tag(v___y_8702_) == 0 {
                    v___x_8709_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_8662_ = v___y_8687_;
                    v___y_8663_ = v___y_8688_;
                    v___y_8664_ = v___y_8689_;
                    v___y_8665_ = v___y_8690_;
                    v___y_8666_ = v___y_8691_;
                    v___y_8667_ = v___y_8692_;
                    v___y_8668_ = v___y_8693_;
                    v___y_8669_ = v___y_8694_;
                    v___y_8670_ = v___x_8708_;
                    v___y_8671_ = v___y_8696_;
                    v___y_8672_ = v___y_8695_;
                    v___y_8673_ = v___y_8698_;
                    v___y_8674_ = v___y_8697_;
                    v___y_8675_ = v___y_8699_;
                    v___y_8676_ = v___y_8700_;
                    v___y_8677_ = v___y_8701_;
                    v___y_8678_ = v___y_8702_;
                    v___y_8679_ = v___y_8703_;
                    v___y_8680_ = v___y_8704_;
                    v___y_8681_ = v___y_8705_;
                    v___y_8682_ = v___x_8709_;
                    state = 19;
                    continue;
                } else {
                    v_val_8710_ = lean_ctor_get(v___y_8702_, 0);
                    v___x_8711_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    lean_inc(v_val_8710_);
                    v___x_8712_ = lean_array_push(v___x_8711_, v_val_8710_);
                    v___y_8662_ = v___y_8687_;
                    v___y_8663_ = v___y_8688_;
                    v___y_8664_ = v___y_8689_;
                    v___y_8665_ = v___y_8690_;
                    v___y_8666_ = v___y_8691_;
                    v___y_8667_ = v___y_8692_;
                    v___y_8668_ = v___y_8693_;
                    v___y_8669_ = v___y_8694_;
                    v___y_8670_ = v___x_8708_;
                    v___y_8671_ = v___y_8696_;
                    v___y_8672_ = v___y_8695_;
                    v___y_8673_ = v___y_8698_;
                    v___y_8674_ = v___y_8697_;
                    v___y_8675_ = v___y_8699_;
                    v___y_8676_ = v___y_8700_;
                    v___y_8677_ = v___y_8701_;
                    v___y_8678_ = v___y_8702_;
                    v___y_8679_ = v___y_8703_;
                    v___y_8680_ = v___y_8704_;
                    v___y_8681_ = v___y_8705_;
                    v___y_8682_ = v___x_8712_;
                    state = 19;
                    continue;
                }
            }
            21 => {
                lean_inc_ref(v___y_8730_);
                v___x_8734_ = l_Array_append___redArg(v___y_8730_, v___y_8733_);
                lean_dec_ref(v___y_8733_);
                lean_inc(v___y_8722_);
                lean_inc(v___y_8719_);
                v___x_8735_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_8735_, 0, v___y_8719_);
                lean_ctor_set(v___x_8735_, 1, v___y_8722_);
                lean_ctor_set(v___x_8735_, 2, v___x_8734_);
                if lean_obj_tag(v___y_8720_) == 1 {
                    v_val_8736_ = lean_ctor_get(v___y_8720_, 0);
                    lean_inc(v_val_8736_);
                    lean_dec_ref_known(v___y_8720_, 1);
                    v___x_8737_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
                    lean_inc_n(v___y_8719_, 3);
                    v___x_8738_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_8738_, 0, v___y_8719_);
                    lean_ctor_set(v___x_8738_, 1, v___x_8737_);
                    lean_inc_ref(v___y_8730_);
                    v___x_8739_ = l_Array_append___redArg(v___y_8730_, v_val_8736_);
                    lean_dec(v_val_8736_);
                    lean_inc(v___y_8722_);
                    v___x_8740_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_8740_, 0, v___y_8719_);
                    lean_ctor_set(v___x_8740_, 1, v___y_8722_);
                    lean_ctor_set(v___x_8740_, 2, v___x_8739_);
                    v___x_8741_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
                    v___x_8742_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_8742_, 0, v___y_8719_);
                    lean_ctor_set(v___x_8742_, 1, v___x_8741_);
                    v___x_8743_ = l_Array_mkArray3___redArg(v___x_8738_, v___x_8740_, v___x_8742_);
                    v___y_8687_ = v___y_8714_;
                    v___y_8688_ = v___y_8715_;
                    v___y_8689_ = v___y_8716_;
                    v___y_8690_ = v___y_8717_;
                    v___y_8691_ = v___y_8718_;
                    v___y_8692_ = v___x_8735_;
                    v___y_8693_ = v___y_8719_;
                    v___y_8694_ = v___y_8721_;
                    v___y_8695_ = v___y_8722_;
                    v___y_8696_ = v___y_8723_;
                    v___y_8697_ = v___y_8724_;
                    v___y_8698_ = v___y_8725_;
                    v___y_8699_ = v___y_8726_;
                    v___y_8700_ = v___y_8727_;
                    v___y_8701_ = v___y_8728_;
                    v___y_8702_ = v___y_8729_;
                    v___y_8703_ = v___y_8730_;
                    v___y_8704_ = v___y_8731_;
                    v___y_8705_ = v___y_8732_;
                    v___y_8706_ = v___x_8743_;
                    state = 20;
                    continue;
                } else {
                    lean_dec(v___y_8720_);
                    v___x_8744_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_8687_ = v___y_8714_;
                    v___y_8688_ = v___y_8715_;
                    v___y_8689_ = v___y_8716_;
                    v___y_8690_ = v___y_8717_;
                    v___y_8691_ = v___y_8718_;
                    v___y_8692_ = v___x_8735_;
                    v___y_8693_ = v___y_8719_;
                    v___y_8694_ = v___y_8721_;
                    v___y_8695_ = v___y_8722_;
                    v___y_8696_ = v___y_8723_;
                    v___y_8697_ = v___y_8724_;
                    v___y_8698_ = v___y_8725_;
                    v___y_8699_ = v___y_8726_;
                    v___y_8700_ = v___y_8727_;
                    v___y_8701_ = v___y_8728_;
                    v___y_8702_ = v___y_8729_;
                    v___y_8703_ = v___y_8730_;
                    v___y_8704_ = v___y_8731_;
                    v___y_8705_ = v___y_8732_;
                    v___y_8706_ = v___x_8744_;
                    state = 20;
                    continue;
                }
            }
            22 => {
                v_ref_8761_ = lean_ctor_get(v___y_8756_, 5);
                v___x_8762_ = l_Lean_SourceInfo_fromRef(v_ref_8761_, v___y_8760_);
                v___x_8763_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0;
                v___x_8764_ =
                    l_Lean_Name_mkStr4(v___x_8441_, v___x_8442_, v___x_8443_, v___x_8763_);
                v___x_8765_ = l_Lean_SourceInfo_fromRef(v_tk_8455_, v___x_8440_);
                v___x_8766_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_8766_, 0, v___x_8765_);
                lean_ctor_set(v___x_8766_, 1, v___x_8763_);
                v___x_8767_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                v___x_8768_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                lean_inc(v___x_8762_);
                v___x_8769_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_8769_, 0, v___x_8762_);
                lean_ctor_set(v___x_8769_, 1, v___x_8767_);
                lean_ctor_set(v___x_8769_, 2, v___x_8768_);
                if lean_obj_tag(v___y_8758_) == 1 {
                    v_val_8770_ = lean_ctor_get(v___y_8758_, 0);
                    lean_inc(v_val_8770_);
                    lean_dec_ref_known(v___y_8758_, 1);
                    v___x_8771_ = l_Lean_SourceInfo_fromRef(v_val_8770_, v___x_8440_);
                    lean_dec(v_val_8770_);
                    v___x_8772_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                    v___x_8773_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_8773_, 0, v___x_8771_);
                    lean_ctor_set(v___x_8773_, 1, v___x_8772_);
                    v___x_8774_ = l_Array_mkArray1___redArg(v___x_8773_);
                    v___y_8630_ = v___y_8746_;
                    v___y_8631_ = v___y_8747_;
                    v___y_8632_ = v___y_8748_;
                    v___y_8633_ = v___y_8749_;
                    v___y_8634_ = v___x_8767_;
                    v___y_8635_ = v___y_8750_;
                    v___y_8636_ = v___x_8764_;
                    v___y_8637_ = v___y_8751_;
                    v___y_8638_ = v___y_8752_;
                    v___y_8639_ = v___y_8753_;
                    v___y_8640_ = v___y_8754_;
                    v___y_8641_ = v___y_8755_;
                    v___y_8642_ = v___y_8756_;
                    v___y_8643_ = v___x_8769_;
                    v___y_8644_ = v___x_8766_;
                    v___y_8645_ = v___y_8757_;
                    v___y_8646_ = v___x_8762_;
                    v___y_8647_ = v___x_8768_;
                    v___y_8648_ = v___y_8759_;
                    v___y_8649_ = v___x_8774_;
                    state = 18;
                    continue;
                } else {
                    lean_dec(v___y_8758_);
                    v___x_8775_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                    v___y_8630_ = v___y_8746_;
                    v___y_8631_ = v___y_8747_;
                    v___y_8632_ = v___y_8748_;
                    v___y_8633_ = v___y_8749_;
                    v___y_8634_ = v___x_8767_;
                    v___y_8635_ = v___y_8750_;
                    v___y_8636_ = v___x_8764_;
                    v___y_8637_ = v___y_8751_;
                    v___y_8638_ = v___y_8752_;
                    v___y_8639_ = v___y_8753_;
                    v___y_8640_ = v___y_8754_;
                    v___y_8641_ = v___y_8755_;
                    v___y_8642_ = v___y_8756_;
                    v___y_8643_ = v___x_8769_;
                    v___y_8644_ = v___x_8766_;
                    v___y_8645_ = v___y_8757_;
                    v___y_8646_ = v___x_8762_;
                    v___y_8647_ = v___x_8768_;
                    v___y_8648_ = v___y_8759_;
                    v___y_8649_ = v___x_8775_;
                    state = 18;
                    continue;
                }
            }
            23 => {
                if lean_obj_tag(v___y_8781_) == 0 {
                    v___x_8791_ = 0;
                    v___y_8746_ = v___y_8777_;
                    v___y_8747_ = v___y_8778_;
                    v___y_8748_ = v___y_8779_;
                    v___y_8749_ = v___y_8780_;
                    v___y_8750_ = v___y_8781_;
                    v___y_8751_ = v___y_8782_;
                    v___y_8752_ = v___y_8783_;
                    v___y_8753_ = v___y_8784_;
                    v___y_8754_ = v___y_8785_;
                    v___y_8755_ = v___y_8786_;
                    v___y_8756_ = v___y_8787_;
                    v___y_8757_ = v___y_8790_;
                    v___y_8758_ = v___y_8788_;
                    v___y_8759_ = v___y_8789_;
                    v___y_8760_ = v___x_8791_;
                    state = 22;
                    continue;
                } else {
                    if v___y_8783_ == 0 {
                        v___y_8746_ = v___y_8777_;
                        v___y_8747_ = v___y_8778_;
                        v___y_8748_ = v___y_8779_;
                        v___y_8749_ = v___y_8780_;
                        v___y_8750_ = v___y_8781_;
                        v___y_8751_ = v___y_8782_;
                        v___y_8752_ = v___y_8783_;
                        v___y_8753_ = v___y_8784_;
                        v___y_8754_ = v___y_8785_;
                        v___y_8755_ = v___y_8786_;
                        v___y_8756_ = v___y_8787_;
                        v___y_8757_ = v___y_8790_;
                        v___y_8758_ = v___y_8788_;
                        v___y_8759_ = v___y_8789_;
                        v___y_8760_ = v___y_8783_;
                        state = 22;
                        continue;
                    } else {
                        v_ref_8792_ = lean_ctor_get(v___y_8787_, 5);
                        v___x_8793_ = 0;
                        v___x_8794_ = l_Lean_SourceInfo_fromRef(v_ref_8792_, v___x_8793_);
                        v___x_8795_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1;
                        v___x_8796_ =
                            l_Lean_Name_mkStr4(v___x_8441_, v___x_8442_, v___x_8443_, v___x_8795_);
                        v___x_8797_ = l_Lean_SourceInfo_fromRef(v_tk_8455_, v___x_8440_);
                        v___x_8798_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2;
                        v___x_8799_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_8799_, 0, v___x_8797_);
                        lean_ctor_set(v___x_8799_, 1, v___x_8798_);
                        v___x_8800_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__3;
                        v___x_8801_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_evalSimpTrace_spec__2___redArg___closed__4);
                        lean_inc(v___x_8794_);
                        v___x_8802_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_8802_, 0, v___x_8794_);
                        lean_ctor_set(v___x_8802_, 1, v___x_8800_);
                        lean_ctor_set(v___x_8802_, 2, v___x_8801_);
                        if lean_obj_tag(v___y_8788_) == 1 {
                            v_val_8803_ = lean_ctor_get(v___y_8788_, 0);
                            lean_inc(v_val_8803_);
                            lean_dec_ref_known(v___y_8788_, 1);
                            v___x_8804_ = l_Lean_SourceInfo_fromRef(v_val_8803_, v___x_8440_);
                            lean_dec(v_val_8803_);
                            v___x_8805_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
                            v___x_8806_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_8806_, 0, v___x_8804_);
                            lean_ctor_set(v___x_8806_, 1, v___x_8805_);
                            v___x_8807_ = l_Array_mkArray1___redArg(v___x_8806_);
                            v___y_8714_ = v___y_8777_;
                            v___y_8715_ = v___y_8778_;
                            v___y_8716_ = v___y_8779_;
                            v___y_8717_ = v___y_8780_;
                            v___y_8718_ = v___y_8781_;
                            v___y_8719_ = v___x_8794_;
                            v___y_8720_ = v___y_8782_;
                            v___y_8721_ = v___y_8783_;
                            v___y_8722_ = v___x_8800_;
                            v___y_8723_ = v___y_8784_;
                            v___y_8724_ = v___y_8786_;
                            v___y_8725_ = v___y_8785_;
                            v___y_8726_ = v___y_8787_;
                            v___y_8727_ = v___x_8799_;
                            v___y_8728_ = v___x_8802_;
                            v___y_8729_ = v___y_8790_;
                            v___y_8730_ = v___x_8801_;
                            v___y_8731_ = v___x_8796_;
                            v___y_8732_ = v___y_8789_;
                            v___y_8733_ = v___x_8807_;
                            state = 21;
                            continue;
                        } else {
                            lean_dec(v___y_8788_);
                            v___x_8808_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
                            v___y_8714_ = v___y_8777_;
                            v___y_8715_ = v___y_8778_;
                            v___y_8716_ = v___y_8779_;
                            v___y_8717_ = v___y_8780_;
                            v___y_8718_ = v___y_8781_;
                            v___y_8719_ = v___x_8794_;
                            v___y_8720_ = v___y_8782_;
                            v___y_8721_ = v___y_8783_;
                            v___y_8722_ = v___x_8800_;
                            v___y_8723_ = v___y_8784_;
                            v___y_8724_ = v___y_8786_;
                            v___y_8725_ = v___y_8785_;
                            v___y_8726_ = v___y_8787_;
                            v___y_8727_ = v___x_8799_;
                            v___y_8728_ = v___x_8802_;
                            v___y_8729_ = v___y_8790_;
                            v___y_8730_ = v___x_8801_;
                            v___y_8731_ = v___x_8796_;
                            v___y_8732_ = v___y_8789_;
                            v___y_8733_ = v___x_8808_;
                            state = 21;
                            continue;
                        }
                    }
                }
            }
            24 => {
                v___x_8824_ = lean_unsigned_to_nat(3);
                v___x_8825_ = l_Lean_Syntax_getArg(v___y_8813_, v___x_8824_);
                lean_dec(v___y_8813_);
                v___x_8826_ = l_Lean_Syntax_getOptional_x3f(v___x_8825_);
                lean_dec(v___x_8825_);
                if lean_obj_tag(v___x_8826_) == 0 {
                    v___x_8827_ = lean_box(0);
                    v___y_8777_ = v___y_8823_;
                    v___y_8778_ = v___y_8816_;
                    v___y_8779_ = v___y_8817_;
                    v___y_8780_ = v___y_8819_;
                    v___y_8781_ = v___y_8810_;
                    v___y_8782_ = v_args_8815_;
                    v___y_8783_ = v___y_8811_;
                    v___y_8784_ = v___y_8820_;
                    v___y_8785_ = v___y_8821_;
                    v___y_8786_ = v___y_8818_;
                    v___y_8787_ = v___y_8822_;
                    v___y_8788_ = v___y_8812_;
                    v___y_8789_ = v___y_8814_;
                    v___y_8790_ = v___x_8827_;
                    state = 23;
                    continue;
                } else {
                    v_val_8828_ = lean_ctor_get(v___x_8826_, 0);
                    v_isSharedCheck_8835_ = (!lean_is_exclusive(v___x_8826_)) as u8;
                    if v_isSharedCheck_8835_ == 0 {
                        v___x_8830_ = v___x_8826_;
                        v_isShared_8831_ = v_isSharedCheck_8835_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_val_8828_);
                        lean_dec(v___x_8826_);
                        v___x_8830_ = lean_box(0);
                        v_isShared_8831_ = v_isSharedCheck_8835_;
                        state = 25;
                        continue;
                    }
                }
            }
            25 => {
                if v_isShared_8831_ == 0 {
                    v___x_8833_ = v___x_8830_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_8834_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8834_, 0, v_val_8828_);
                    v___x_8833_ = v_reuseFailAlloc_8834_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___y_8777_ = v___y_8823_;
                v___y_8778_ = v___y_8816_;
                v___y_8779_ = v___y_8817_;
                v___y_8780_ = v___y_8819_;
                v___y_8781_ = v___y_8810_;
                v___y_8782_ = v_args_8815_;
                v___y_8783_ = v___y_8811_;
                v___y_8784_ = v___y_8820_;
                v___y_8785_ = v___y_8821_;
                v___y_8786_ = v___y_8818_;
                v___y_8787_ = v___y_8822_;
                v___y_8788_ = v___y_8812_;
                v___y_8789_ = v___y_8814_;
                v___y_8790_ = v___x_8833_;
                state = 23;
                continue;
            }
            27 => {
                v___x_8852_ = l_Lean_Syntax_getArg(v___y_8841_, v___y_8839_);
                v___x_8853_ = l_Lean_Syntax_isNone(v___x_8852_);
                if v___x_8853_ == 0 {
                    lean_inc(v___x_8852_);
                    v___x_8854_ = l_Lean_Syntax_matchesNull(v___x_8852_, v___x_8836_);
                    if v___x_8854_ == 0 {
                        lean_dec(v___x_8852_);
                        lean_dec(v_o_8843_);
                        lean_dec(v___y_8842_);
                        lean_dec(v___y_8841_);
                        lean_dec(v___y_8838_);
                        lean_dec(v_tk_8455_);
                        lean_dec_ref(v___x_8443_);
                        lean_dec_ref(v___x_8442_);
                        lean_dec_ref(v___x_8441_);
                        v___x_8855_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                        return v___x_8855_;
                    } else {
                        v___x_8856_ = l_Lean_Syntax_getArg(v___x_8852_, v___x_8454_);
                        lean_dec(v___x_8852_);
                        v___x_8857_ = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__1___closed__12;
                        lean_inc_ref(v___x_8443_);
                        lean_inc_ref(v___x_8442_);
                        lean_inc_ref(v___x_8441_);
                        v___x_8858_ =
                            l_Lean_Name_mkStr4(v___x_8441_, v___x_8442_, v___x_8443_, v___x_8857_);
                        lean_inc(v___x_8856_);
                        v___x_8859_ = l_Lean_Syntax_isOfKind(v___x_8856_, v___x_8858_);
                        lean_dec(v___x_8858_);
                        if v___x_8859_ == 0 {
                            lean_dec(v___x_8856_);
                            lean_dec(v_o_8843_);
                            lean_dec(v___y_8842_);
                            lean_dec(v___y_8841_);
                            lean_dec(v___y_8838_);
                            lean_dec(v_tk_8455_);
                            lean_dec_ref(v___x_8443_);
                            lean_dec_ref(v___x_8442_);
                            lean_dec_ref(v___x_8441_);
                            v___x_8860_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                            return v___x_8860_;
                        } else {
                            v___x_8861_ = l_Lean_Syntax_getArg(v___x_8856_, v___x_8836_);
                            lean_dec(v___x_8856_);
                            v_args_8862_ = l_Lean_Syntax_getArgs(v___x_8861_);
                            lean_dec(v___x_8861_);
                            v___x_8863_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_8863_, 0, v_args_8862_);
                            v___y_8810_ = v___y_8838_;
                            v___y_8811_ = v___y_8840_;
                            v___y_8812_ = v_o_8843_;
                            v___y_8813_ = v___y_8841_;
                            v___y_8814_ = v___y_8842_;
                            v_args_8815_ = v___x_8863_;
                            v___y_8816_ = v___y_8844_;
                            v___y_8817_ = v___y_8845_;
                            v___y_8818_ = v___y_8846_;
                            v___y_8819_ = v___y_8847_;
                            v___y_8820_ = v___y_8848_;
                            v___y_8821_ = v___y_8849_;
                            v___y_8822_ = v___y_8850_;
                            v___y_8823_ = v___y_8851_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_8852_);
                    v___x_8864_ = lean_box(0);
                    v___y_8810_ = v___y_8838_;
                    v___y_8811_ = v___y_8840_;
                    v___y_8812_ = v_o_8843_;
                    v___y_8813_ = v___y_8841_;
                    v___y_8814_ = v___y_8842_;
                    v_args_8815_ = v___x_8864_;
                    v___y_8816_ = v___y_8844_;
                    v___y_8817_ = v___y_8845_;
                    v___y_8818_ = v___y_8846_;
                    v___y_8819_ = v___y_8847_;
                    v___y_8820_ = v___y_8848_;
                    v___y_8821_ = v___y_8849_;
                    v___y_8822_ = v___y_8850_;
                    v___y_8823_ = v___y_8851_;
                    state = 24;
                    continue;
                }
            }
            28 => {
                v___x_8875_ = lean_unsigned_to_nat(2);
                v___x_8876_ = l_Lean_Syntax_getArg(v_stx_8439_, v___x_8875_);
                v___x_8877_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3;
                lean_inc_ref(v___x_8443_);
                lean_inc_ref(v___x_8442_);
                lean_inc_ref(v___x_8441_);
                v___x_8878_ =
                    l_Lean_Name_mkStr4(v___x_8441_, v___x_8442_, v___x_8443_, v___x_8877_);
                lean_inc(v___x_8876_);
                v___x_8879_ = l_Lean_Syntax_isOfKind(v___x_8876_, v___x_8878_);
                lean_dec(v___x_8878_);
                if v___x_8879_ == 0 {
                    lean_dec(v___x_8876_);
                    lean_dec(v_bang_8866_);
                    lean_dec(v_tk_8455_);
                    lean_dec_ref(v___x_8443_);
                    lean_dec_ref(v___x_8442_);
                    lean_dec_ref(v___x_8441_);
                    v___x_8880_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                    return v___x_8880_;
                } else {
                    v___x_8881_ = l_Lean_Syntax_getArg(v___x_8876_, v___x_8454_);
                    v___x_8882_ = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15;
                    lean_inc_ref(v___x_8443_);
                    lean_inc_ref(v___x_8442_);
                    lean_inc_ref(v___x_8441_);
                    v___x_8883_ =
                        l_Lean_Name_mkStr4(v___x_8441_, v___x_8442_, v___x_8443_, v___x_8882_);
                    lean_inc(v___x_8881_);
                    v___x_8884_ = l_Lean_Syntax_isOfKind(v___x_8881_, v___x_8883_);
                    lean_dec(v___x_8883_);
                    if v___x_8884_ == 0 {
                        lean_dec(v___x_8881_);
                        lean_dec(v___x_8876_);
                        lean_dec(v_bang_8866_);
                        lean_dec(v_tk_8455_);
                        lean_dec_ref(v___x_8443_);
                        lean_dec_ref(v___x_8442_);
                        lean_dec_ref(v___x_8441_);
                        v___x_8885_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                        return v___x_8885_;
                    } else {
                        v___x_8886_ = l_Lean_Syntax_getArg(v___x_8876_, v___x_8836_);
                        v___x_8887_ = l_Lean_Syntax_isNone(v___x_8886_);
                        if v___x_8887_ == 0 {
                            lean_inc(v___x_8886_);
                            v___x_8888_ = l_Lean_Syntax_matchesNull(v___x_8886_, v___x_8836_);
                            if v___x_8888_ == 0 {
                                lean_dec(v___x_8886_);
                                lean_dec(v___x_8881_);
                                lean_dec(v___x_8876_);
                                lean_dec(v_bang_8866_);
                                lean_dec(v_tk_8455_);
                                lean_dec_ref(v___x_8443_);
                                lean_dec_ref(v___x_8442_);
                                lean_dec_ref(v___x_8441_);
                                v___x_8889_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg();
                                return v___x_8889_;
                            } else {
                                v_o_8890_ = l_Lean_Syntax_getArg(v___x_8886_, v___x_8454_);
                                lean_dec(v___x_8886_);
                                v___x_8891_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_8891_, 0, v_o_8890_);
                                v___y_8838_ = v_bang_8866_;
                                v___y_8839_ = v___x_8875_;
                                v___y_8840_ = v___x_8884_;
                                v___y_8841_ = v___x_8876_;
                                v___y_8842_ = v___x_8881_;
                                v_o_8843_ = v___x_8891_;
                                v___y_8844_ = v___y_8867_;
                                v___y_8845_ = v___y_8868_;
                                v___y_8846_ = v___y_8869_;
                                v___y_8847_ = v___y_8870_;
                                v___y_8848_ = v___y_8871_;
                                v___y_8849_ = v___y_8872_;
                                v___y_8850_ = v___y_8873_;
                                v___y_8851_ = v___y_8874_;
                                state = 27;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_8886_);
                            v___x_8892_ = lean_box(0);
                            v___y_8838_ = v_bang_8866_;
                            v___y_8839_ = v___x_8875_;
                            v___y_8840_ = v___x_8884_;
                            v___y_8841_ = v___x_8876_;
                            v___y_8842_ = v___x_8881_;
                            v_o_8843_ = v___x_8892_;
                            v___y_8844_ = v___y_8867_;
                            v___y_8845_ = v___y_8868_;
                            v___y_8846_ = v___y_8869_;
                            v___y_8847_ = v___y_8870_;
                            v___y_8848_ = v___y_8871_;
                            v___y_8849_ = v___y_8872_;
                            v___y_8850_ = v___y_8873_;
                            v___y_8851_ = v___y_8874_;
                            state = 27;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(
    mut v___x_8900_: *mut LeanObject,
    mut v_stx_8901_: *mut LeanObject,
    mut v___x_8902_: *mut LeanObject,
    mut v___x_8903_: *mut LeanObject,
    mut v___x_8904_: *mut LeanObject,
    mut v___x_8905_: *mut LeanObject,
    mut v___y_8906_: *mut LeanObject,
    mut v___y_8907_: *mut LeanObject,
    mut v___y_8908_: *mut LeanObject,
    mut v___y_8909_: *mut LeanObject,
    mut v___y_8910_: *mut LeanObject,
    mut v___y_8911_: *mut LeanObject,
    mut v___y_8912_: *mut LeanObject,
    mut v___y_8913_: *mut LeanObject,
    mut v___y_8914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10541__boxed_8915_: u8 = 0;
    let mut v___x_10542__boxed_8916_: u8 = 0;
    let mut v_res_8917_: *mut LeanObject = core::ptr::null_mut();
    v___x_10541__boxed_8915_ = (lean_unbox(v___x_8900_) as u8);
    v___x_10542__boxed_8916_ = (lean_unbox(v___x_8902_) as u8);
    v_res_8917_ = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(
        v___x_10541__boxed_8915_,
        v_stx_8901_,
        v___x_10542__boxed_8916_,
        v___x_8903_,
        v___x_8904_,
        v___x_8905_,
        v___y_8906_,
        v___y_8907_,
        v___y_8908_,
        v___y_8909_,
        v___y_8910_,
        v___y_8911_,
        v___y_8912_,
        v___y_8913_,
    );
    lean_dec(v___y_8913_);
    lean_dec_ref(v___y_8912_);
    lean_dec(v___y_8911_);
    lean_dec_ref(v___y_8910_);
    lean_dec(v___y_8909_);
    lean_dec_ref(v___y_8908_);
    lean_dec(v___y_8907_);
    lean_dec_ref(v___y_8906_);
    lean_dec(v_stx_8901_);
    return v_res_8917_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalDSimpTrace(
    mut v_stx_8924_: *mut LeanObject,
    mut v_a_8925_: *mut LeanObject,
    mut v_a_8926_: *mut LeanObject,
    mut v_a_8927_: *mut LeanObject,
    mut v_a_8928_: *mut LeanObject,
    mut v_a_8929_: *mut LeanObject,
    mut v_a_8930_: *mut LeanObject,
    mut v_a_8931_: *mut LeanObject,
    mut v_a_8932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8938_: u8 = 0;
    let mut v___x_8939_: u8 = 0;
    let mut v___x_8940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8944_: *mut LeanObject = core::ptr::null_mut();
    v___x_8934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__0;
    v___x_8935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__1;
    v___x_8936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterSuggestionsAndLocalsFromSimpConfig_spec__0___closed__2;
    v___x_8937_ = l_Lean_Elab_Tactic_evalDSimpTrace___closed__1;
    lean_inc(v_stx_8924_);
    v___x_8938_ = l_Lean_Syntax_isOfKind(v_stx_8924_, v___x_8937_);
    v___x_8939_ = 1;
    v___x_8940_ = lean_box((v___x_8938_) as usize);
    v___x_8941_ = lean_box((v___x_8939_) as usize);
    v___y_8942_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed as *mut core::ffi::c_void,
        15,
        6,
    );
    lean_closure_set(v___y_8942_, 0, v___x_8940_);
    lean_closure_set(v___y_8942_, 1, v_stx_8924_);
    lean_closure_set(v___y_8942_, 2, v___x_8941_);
    lean_closure_set(v___y_8942_, 3, v___x_8934_);
    lean_closure_set(v___y_8942_, 4, v___x_8935_);
    lean_closure_set(v___y_8942_, 5, v___x_8936_);
    v___x_8943_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_withSimpDiagnostics___boxed as *mut core::ffi::c_void,
        10,
        1,
    );
    lean_closure_set(v___x_8943_, 0, v___y_8942_);
    v___x_8944_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___x_8943_,
        v_a_8925_,
        v_a_8926_,
        v_a_8927_,
        v_a_8928_,
        v_a_8929_,
        v_a_8930_,
        v_a_8931_,
        v_a_8932_,
    );
    return v___x_8944_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalDSimpTrace___boxed(
    mut v_stx_8945_: *mut LeanObject,
    mut v_a_8946_: *mut LeanObject,
    mut v_a_8947_: *mut LeanObject,
    mut v_a_8948_: *mut LeanObject,
    mut v_a_8949_: *mut LeanObject,
    mut v_a_8950_: *mut LeanObject,
    mut v_a_8951_: *mut LeanObject,
    mut v_a_8952_: *mut LeanObject,
    mut v_a_8953_: *mut LeanObject,
    mut v_a_8954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8955_: *mut LeanObject = core::ptr::null_mut();
    v_res_8955_ = l_Lean_Elab_Tactic_evalDSimpTrace(
        v_stx_8945_,
        v_a_8946_,
        v_a_8947_,
        v_a_8948_,
        v_a_8949_,
        v_a_8950_,
        v_a_8951_,
        v_a_8952_,
        v_a_8953_,
    );
    lean_dec(v_a_8953_);
    lean_dec_ref(v_a_8952_);
    lean_dec(v_a_8951_);
    lean_dec_ref(v_a_8950_);
    lean_dec(v_a_8949_);
    lean_dec_ref(v_a_8948_);
    lean_dec(v_a_8947_);
    lean_dec_ref(v_a_8946_);
    return v_res_8955_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1()
-> *mut LeanObject {
    let mut v___x_8963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8967_: *mut LeanObject = core::ptr::null_mut();
    v___x_8963_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_8964_ = l_Lean_Elab_Tactic_evalDSimpTrace___closed__1;
    v___x_8965_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1;
    v___x_8966_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalDSimpTrace___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_8967_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_8963_,
        v___x_8964_,
        v___x_8965_,
        v___x_8966_,
    );
    return v___x_8967_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___boxed(
    mut v_a_8968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8969_: *mut LeanObject = core::ptr::null_mut();
    v_res_8969_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
    return v_res_8969_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3()
-> *mut LeanObject {
    let mut v___x_8996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8998_: *mut LeanObject = core::ptr::null_mut();
    v___x_8996_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1;
    v___x_8997_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6;
    v___x_8998_ = l_Lean_addBuiltinDeclarationRanges(v___x_8996_, v___x_8997_);
    return v___x_8998_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___boxed(
    mut v_a_8999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9000_: *mut LeanObject = core::ptr::null_mut();
    v_res_9000_ = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
    return v_res_9000_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_SimpTrace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ElabRules(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_SimpTrace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_SimpTrace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ElabRules(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_LibrarySuggestions_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_SimpTrace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_SimpTrace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_SimpTrace(builtin);
}
