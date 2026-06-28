// Lean compiler output
// Module: Lean.Meta.Tactic.TryThis
// Imports: Lean.Server.CodeActions Lean.Meta.Tactic.ExposeNames Lean.Widget.UserWidget Lean.Widget.UserWidget
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_SepArray_ofElems, lean_mk_syntax_ident};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_Syntax_node5, l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::CoreM::{l_Lean_Exception_isRuntime, l_Lean_diagnostics};
use crate::r#gen::Lean::Data::Lsp::Basic::l_Lean_Lsp_WorkspaceEdit_ofTextEdit;
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_FileMap_utf8RangeToLspRange;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_SavedState_restore___redArg, l_Lean_Elab_Tactic_evalTactic___boxed,
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_saveState___redArg,
    l_Lean_Elab_Tactic_withoutRecover___boxed,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_withoutErrToSorryImp___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_Expr_isConst};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_joinSep,
    l_Lean_MessageData_nil, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageData_sbracket, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::Meta::Hint::{
    l_Lean_Meta_Hint_mkSuggestionsMessage, l_Lean_Meta_Hint_textInsertionWidget,
    l_Lean_Meta_Hint_tryThisDiffWidget,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Tactic::ExposeNames::{
    initialize_Lean_Meta_Tactic_ExposeNames, l_Lean_Meta_withExposedNames___redArg,
    runtime_initialize_Lean_Meta_Tactic_ExposeNames,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::Meta::TryThis::l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Basic::l_Lean_PrettyPrinter_delab;
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Options::{
    l_Lean_pp_mvars, l_Lean_pp_mvars_anonymous,
};
use crate::r#gen::Lean::PrettyPrinter::{
    l_Lean_MessageData_ofConst, l_Lean_PrettyPrinter_ppExpr___boxed,
};
use crate::r#gen::Lean::Server::CodeActions::Basic::l_Lean_Server_addBuiltinCodeActionProvider;
use crate::r#gen::Lean::Server::CodeActions::{
    initialize_Lean_Server_CodeActions, runtime_initialize_Lean_Server_CodeActions,
};
use crate::r#gen::Lean::Server::FileWorker::Utils::l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier;
use crate::r#gen::Lean::Server::InfoUtils::l_Lean_Elab_InfoTree_foldInfo___redArg;
use crate::r#gen::Lean::Server::Snapshots::l_Lean_Server_Snapshots_Snapshot_infoTree;
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_getRange_x3f;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Widget::UserWidget::{
    initialize_Lean_Widget_UserWidget, l_Lean_Widget_addBuiltinModule,
    meta_initialize_Lean_Widget_UserWidget, runtime_initialize_Lean_Widget_UserWidget,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_dec_eq, lean_nat_dec_le, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 105, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [116, 114, 121, 84, 104, 105, 115, 68, 105, 102, 102, 87, 105, 100, 103, 101, 116, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2_value) as *mut LeanObject,15479558908960879501 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3_value) as *mut LeanObject,647364315083554222 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [116, 101, 120, 116, 73, 110, 115, 101, 114, 116, 105, 111, 110, 87, 105, 100, 103, 101, 116, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2_value) as *mut LeanObject,15479558908960879501 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__0_value) as *mut LeanObject,6343280674608731273 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [113, 117, 105, 99, 107, 102, 105, 120, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__0_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18261494228143523011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__6_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [84, 114, 121, 84, 104, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__6_value) as *mut LeanObject,11825428210741116515 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__7_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,1116595739608176686 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,17813167199459642711 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value) as *mut LeanObject,15677756058513895175 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__10_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,16834691049419862406 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__6_value) as *mut LeanObject,17121981855113759930 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__13_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [116, 114, 121, 84, 104, 105, 115, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__13_value) as *mut LeanObject,17196397306749004113 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__14_value) as *mut LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__0_value:
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
    m_data: [116, 101, 114, 109, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__0_value)
            as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__1_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__4_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__0_value: LeanStringObject<
    25,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        78, 111, 32, 115, 117, 103, 103, 101, 115, 116, 105, 111, 110, 115, 32, 97, 118, 97, 105,
        108, 97, 98, 108, 101, 0,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__0_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [84, 97, 99, 116, 105, 99, 32, 100, 105, 100, 32, 110, 111, 116, 32, 112, 114, 111, 100, 117, 99, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 103, 111, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1_value) as *mut LeanObject,8689124066155232629 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 112, 111, 115, 101, 78, 97, 109, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10_value) as *mut LeanObject,11647286487098892037 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 112, 111, 115, 101, 95, 110, 97, 109, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [40, 101, 120, 112, 111, 115, 101, 95, 110, 97, 109, 101, 115, 59, 32, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 111, 117, 110, 100, 32, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [44, 32, 98, 117, 116, 32, 116, 104, 101, 32, 99, 111, 114, 114, 101, 115, 112, 111, 110, 100, 105, 110, 103, 32, 116, 97, 99, 116, 105, 99, 32, 102, 97, 105, 108, 101, 100, 58, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4_value: LeanStringObject<163> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 163, m_capacity: 163, m_length: 162, m_data: [10, 10, 73, 116, 32, 109, 97, 121, 32, 98, 101, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 116, 111, 32, 99, 111, 114, 114, 101, 99, 116, 32, 116, 104, 105, 115, 32, 112, 114, 111, 111, 102, 32, 98, 121, 32, 97, 100, 100, 105, 110, 103, 32, 116, 121, 112, 101, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 115, 44, 32, 101, 120, 112, 108, 105, 99, 105, 116, 108, 121, 32, 115, 112, 101, 99, 105, 102, 121, 105, 110, 103, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 44, 32, 111, 114, 32, 101, 108, 105, 109, 105, 110, 97, 116, 105, 110, 103, 32, 117, 110, 110, 101, 99, 101, 115, 115, 97, 114, 121, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 97, 98, 115, 116, 114, 97, 99, 116, 105, 111, 110, 115, 46, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 120, 97, 99, 116, 32, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 102, 105, 110, 101, 32, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 97, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4_value) as *mut LeanObject,14997215300048349804 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 102, 105, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6_value) as *mut LeanObject,17704266427038597681 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 6, m_data: [10, 45, 45, 32, 226, 138, 162, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0_value) as *mut LeanObject,16145843736367156323 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 114, 111, 111, 102, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [10, 45, 45, 32, 82, 101, 109, 97, 105, 110, 105, 110, 103, 32, 115, 117, 98, 103, 111, 97, 108, 115, 58, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__5_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [97, 32, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__7_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 97, 114, 116, 105, 97, 108, 32, 0]};
static mut l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0_value: LeanStringObject<10> =
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
static mut l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2_value: LeanStringObject<11> =
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
        m_data: [84, 114, 121, 32, 116, 104, 101, 115, 101, 58, 0],
    };
static mut l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__0_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [116, 97, 99, 116, 105, 99, 76, 101, 116, 95, 95, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value: LeanCtorObject<
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__0_value)
            as *mut LeanObject,
        17850414294269139746 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [108, 101, 116, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__4_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value_aux_2:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value: LeanCtorObject<
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__4_value)
            as *mut LeanObject,
        17404204824591055365 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__7_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [108, 101, 116, 68, 101, 99, 108, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__7_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value_aux_2:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value: LeanCtorObject<
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__7_value)
            as *mut LeanObject,
        8036185514257755965 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__9_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__9_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value_aux_2:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__9_value)
            as *mut LeanObject,
        17116161260408496210 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__11_value:
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
    m_data: [108, 101, 116, 73, 100, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__11_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value_aux_2:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__11_value
        ) as *mut LeanObject,
        13708106407786339395 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 61, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__14_value:
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
    m_data: [108, 101, 116, 32, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__16_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__18_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__18_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value_aux_2:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__18_value
        ) as *mut LeanObject,
        4498178684837002829 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20_value:
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
    m_data: [58, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__21_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 58, 32, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__21_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__23_value:
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
    m_data: [95, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24_value:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__23_value
        ) as *mut LeanObject,
        13286986945483979944 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__25_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [116, 97, 99, 116, 105, 99, 72, 97, 118, 101, 95, 95, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__25_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__25_value
        ) as *mut LeanObject,
        1823850105022903353 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27_value:
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
    m_data: [104, 97, 118, 101, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__28_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__28_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29_value:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__28_value
        ) as *mut LeanObject,
        9871775667037945883 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30: *mut LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,15353829308266697735 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__6_value) as *mut LeanObject,8327623967363774415 as *mut LeanObject] };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__32_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__32_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__33_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__33_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__33_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__33_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__33_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__35_value:
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
        80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__35_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__36_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__36_value:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__36_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__35_value
        ) as *mut LeanObject,
        300274991653824376 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__36_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__36_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__40_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__40_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__40_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__40_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__40_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__42_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__42_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__43_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__42_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__43_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__44_value:
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
    m_data: [83, 101, 114, 118, 101, 114, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__44_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__45_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [82, 101, 113, 117, 101, 115, 116, 77, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__45_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value_aux_1:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__44_value
        ) as *mut LeanObject,
        15371898625421214203 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__45_value
        ) as *mut LeanObject,
        3569751576455632824 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__47_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__47_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__48_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__48_value:
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
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__48_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__44_value
        ) as *mut LeanObject,
        15371898625421214203 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__48_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__49_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__48_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__49_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,15353829308266697735 as *mut LeanObject] };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__51_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__51_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__52_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__43_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__52_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__53_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__52_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__53_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__54_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__53_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__54_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__55_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__51_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__54_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__55_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__56_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__55_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__56_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__57_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__56_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__57: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__57_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__58_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__57_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__58: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__58_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__59_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__58_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__59: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__59_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__60_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__59_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__60: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__60_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__61_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__60_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__61: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__61_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__62_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__49_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__61_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__62: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__62_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__63_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__49_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__62_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__63: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__63_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__64_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__47_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__63_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__64: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__64_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__65_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__47_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__64_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__65: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__65_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__66_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__43_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__65_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__66: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__66_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__67_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__66_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__67: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__67_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__68_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__67_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__68: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__68_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__69_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__68_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__69: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__69_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__70_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__69_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__70: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__70_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__71_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__70_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__71: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__71_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__72_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__71_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__72: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__72_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__73_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__72_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__73: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__73_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__74_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__73_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__74: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__74_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__75_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__74_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__75: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__75_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__76_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__75_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__76: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__76_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__77_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__76_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__77: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__77_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__78_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__77_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__78: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__78_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__32_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__78_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__80_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [104, 97, 118, 101, 32, 58, 32, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__80: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__80_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__82_value:
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
    m_data: [104, 97, 118, 101, 32, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__82: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__82_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__84_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [104, 97, 118, 101, 32, 58, 61, 32, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__84: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__84_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__0_value: LeanStringObject<8> =
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
        m_data: [97, 32, 112, 114, 111, 111, 102, 0],
    };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 134, 144, 32, 0]};
static mut l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 119, 82, 117, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__0_value) as *mut LeanObject,8860902369834437795 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 144, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__0_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [10, 45, 45, 32, 110, 111, 32, 103, 111, 97, 108, 115, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__2_value:
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
    m_data: [10, 45, 45, 32, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__5_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [44, 32, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__6_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__5_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__8_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 119, 32, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__10_value:
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
    m_data: [32, 97, 116, 32, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__12_value:
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
    m_data: [44, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__13_value:
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
    m_data: [114, 119, 83, 101, 113, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__13_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value:
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
            l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__13_value
        ) as *mut LeanObject,
        11075965128531316786 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__15_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [114, 119, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__16_value:
    LeanStringObject<10> = LeanStringObject {
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
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__16_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value:
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
            l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__16_value
        ) as *mut LeanObject,
        3488656302031949961 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__18_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [114, 119, 82, 117, 108, 101, 83, 101, 113, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__18_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value:
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
            l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__18_value
        ) as *mut LeanObject,
        7234207980690920618 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__20_value:
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
    m_data: [91, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__21_value:
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
    m_data: [93, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22_value:
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
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__23_value:
    LeanStringObject<9> = LeanStringObject {
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
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__23_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value:
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
            l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__23_value
        ) as *mut LeanObject,
        1767494567867404924 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__25_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [97, 116, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__25_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__26_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [108, 111, 99, 97, 116, 105, 111, 110, 72, 121, 112, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__26_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value:
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
            l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__26_value
        ) as *mut LeanObject,
        12722427251967365861 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__0_value: LeanStringObject<28> =
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
            97, 110, 32, 97, 112, 112, 108, 105, 99, 97, 98, 108, 101, 32, 114, 101, 119, 114, 105,
            116, 101, 32, 108, 101, 109, 109, 97, 0,
        ],
    };
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1()
-> *mut LeanObject {
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    v___x_3383_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4;
    v___x_3384_ = l_Lean_Meta_Hint_tryThisDiffWidget;
    v___x_3385_ = l_Lean_Widget_addBuiltinModule(v___x_3383_, v___x_3384_);
    return v___x_3385_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___boxed(
    mut v_a_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3387_: *mut LeanObject = core::ptr::null_mut();
    v_res_3387_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1();
    return v_res_3387_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1()
-> *mut LeanObject {
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    v___x_3395_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1;
    v___x_3396_ = l_Lean_Meta_Hint_textInsertionWidget;
    v___x_3397_ = l_Lean_Widget_addBuiltinModule(v___x_3395_, v___x_3396_);
    return v___x_3397_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___boxed(
    mut v_a_3398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3399_: *mut LeanObject = core::ptr::null_mut();
    v_res_3399_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1();
    return v_res_3399_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(
    mut v___y_3400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_doc_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    v_doc_3402_ = lean_ctor_get(v___y_3400_, 1);
    lean_inc_ref(v_doc_3402_);
    v___x_3403_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3403_, 0, v_doc_3402_);
    return v___x_3403_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___boxed(
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3406_: *mut LeanObject = core::ptr::null_mut();
    v_res_3406_ = l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(v___y_3404_);
    lean_dec_ref(v___y_3404_);
    return v_res_3406_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0(
    mut v___x_3410_: *mut LeanObject,
    mut v_a_3411_: *mut LeanObject,
    mut v_params_3412_: *mut LeanObject,
    mut v___ctx_3413_: *mut LeanObject,
    mut v_info_3414_: *mut LeanObject,
    mut v_result_3415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_edit_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_codeActionTitle_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: u8 = 0;
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_meta_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3430_: u8 = 0;
    let mut v_text_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_end_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_end_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: u8 = 0;
    let mut v_line_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3445_: u8 = 0;
    let mut v___x_3446_: u8 = 0;
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3459_: u8 = 0;
    let mut v_unused_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_info_3414_) == 10 {
                    v_i_3416_ = lean_ctor_get(v_info_3414_, 0);
                    v_stx_3417_ = lean_ctor_get(v_i_3416_, 0);
                    v_value_3418_ = lean_ctor_get(v_i_3416_, 1);
                    v___x_3419_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
                        v_value_3418_,
                        v___x_3410_,
                    );
                    if lean_obj_tag(v___x_3419_) == 1 {
                        v_val_3420_ = lean_ctor_get(v___x_3419_, 0);
                        lean_inc(v_val_3420_);
                        lean_dec_ref_known(v___x_3419_, 1);
                        v_edit_3421_ = lean_ctor_get(v_val_3420_, 0);
                        lean_inc_ref(v_edit_3421_);
                        v_codeActionTitle_3422_ = lean_ctor_get(v_val_3420_, 1);
                        lean_inc_ref(v_codeActionTitle_3422_);
                        lean_dec(v_val_3420_);
                        v___x_3423_ = 0;
                        v___x_3424_ = l_Lean_Syntax_getRange_x3f(v_stx_3417_, v___x_3423_);
                        if lean_obj_tag(v___x_3424_) == 1 {
                            v_toEditableDocumentCore_3425_ = lean_ctor_get(v_a_3411_, 0);
                            v_meta_3426_ = lean_ctor_get(v_toEditableDocumentCore_3425_, 0);
                            v_val_3427_ = lean_ctor_get(v___x_3424_, 0);
                            v_isSharedCheck_3461_ = (!lean_is_exclusive(v___x_3424_)) as u8;
                            if v_isSharedCheck_3461_ == 0 {
                                v___x_3429_ = v___x_3424_;
                                v_isShared_3430_ = v_isSharedCheck_3461_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_val_3427_);
                                lean_dec(v___x_3424_);
                                v___x_3429_ = lean_box(0);
                                v_isShared_3430_ = v_isSharedCheck_3461_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3424_);
                            lean_dec_ref(v_codeActionTitle_3422_);
                            lean_dec_ref(v_edit_3421_);
                            lean_dec_ref(v_a_3411_);
                            return v_result_3415_;
                        }
                    } else {
                        lean_dec(v___x_3419_);
                        lean_dec_ref(v_a_3411_);
                        return v_result_3415_;
                    }
                } else {
                    lean_dec_ref(v_a_3411_);
                    return v_result_3415_;
                }
            }
            1 => {
                v_text_3431_ = lean_ctor_get(v_meta_3426_, 3);
                lean_inc_ref(v_text_3431_);
                v___x_3432_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_3431_, v_val_3427_);
                v_start_3433_ = lean_ctor_get(v___x_3432_, 0);
                lean_inc_ref(v_start_3433_);
                v_range_3434_ = lean_ctor_get(v_params_3412_, 3);
                v_end_3435_ = lean_ctor_get(v_range_3434_, 1);
                v_end_3436_ = lean_ctor_get(v___x_3432_, 1);
                lean_inc_ref(v_end_3436_);
                lean_dec_ref(v___x_3432_);
                v_line_3437_ = lean_ctor_get(v_start_3433_, 0);
                lean_inc(v_line_3437_);
                lean_dec_ref(v_start_3433_);
                v_start_3438_ = lean_ctor_get(v_range_3434_, 0);
                v_line_3439_ = lean_ctor_get(v_end_3435_, 0);
                v___x_3440_ = lean_nat_dec_le(v_line_3437_, v_line_3439_);
                lean_dec(v_line_3437_);
                if v___x_3440_ == 0 {
                    lean_dec_ref(v_end_3436_);
                    lean_del_object(v___x_3429_);
                    lean_dec_ref(v_codeActionTitle_3422_);
                    lean_dec_ref(v_edit_3421_);
                    lean_dec_ref(v_a_3411_);
                    return v_result_3415_;
                } else {
                    v_line_3441_ = lean_ctor_get(v_start_3438_, 0);
                    v_line_3442_ = lean_ctor_get(v_end_3436_, 0);
                    v_isSharedCheck_3459_ = (!lean_is_exclusive(v_end_3436_)) as u8;
                    if v_isSharedCheck_3459_ == 0 {
                        v_unused_3460_ = lean_ctor_get(v_end_3436_, 1);
                        lean_dec(v_unused_3460_);
                        v___x_3444_ = v_end_3436_;
                        v_isShared_3445_ = v_isSharedCheck_3459_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_line_3442_);
                        lean_dec(v_end_3436_);
                        v___x_3444_ = lean_box(0);
                        v_isShared_3445_ = v_isSharedCheck_3459_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3446_ = lean_nat_dec_le(v_line_3441_, v_line_3442_);
                lean_dec(v_line_3442_);
                if v___x_3446_ == 0 {
                    lean_del_object(v___x_3444_);
                    lean_del_object(v___x_3429_);
                    lean_dec_ref(v_codeActionTitle_3422_);
                    lean_dec_ref(v_edit_3421_);
                    lean_dec_ref(v_a_3411_);
                    return v_result_3415_;
                } else {
                    v___x_3447_ = lean_box(0);
                    v___x_3448_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__1;
                    v___x_3449_ =
                        l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_3411_);
                    v___x_3450_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_3449_, v_edit_3421_);
                    if v_isShared_3430_ == 0 {
                        lean_ctor_set(v___x_3429_, 0, v___x_3450_);
                        v___x_3452_ = v___x_3429_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3450_);
                        v___x_3452_ = v_reuseFailAlloc_3458_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3453_ = lean_alloc_ctor(0, 10, (0) as u32);
                lean_ctor_set(v___x_3453_, 0, v___x_3447_);
                lean_ctor_set(v___x_3453_, 1, v___x_3447_);
                lean_ctor_set(v___x_3453_, 2, v_codeActionTitle_3422_);
                lean_ctor_set(v___x_3453_, 3, v___x_3448_);
                lean_ctor_set(v___x_3453_, 4, v___x_3447_);
                lean_ctor_set(v___x_3453_, 5, v___x_3447_);
                lean_ctor_set(v___x_3453_, 6, v___x_3447_);
                lean_ctor_set(v___x_3453_, 7, v___x_3452_);
                lean_ctor_set(v___x_3453_, 8, v___x_3447_);
                lean_ctor_set(v___x_3453_, 9, v___x_3447_);
                if v_isShared_3445_ == 0 {
                    lean_ctor_set(v___x_3444_, 1, v___x_3447_);
                    lean_ctor_set(v___x_3444_, 0, v___x_3453_);
                    v___x_3455_ = v___x_3444_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3453_);
                    lean_ctor_set(v_reuseFailAlloc_3457_, 1, v___x_3447_);
                    v___x_3455_ = v_reuseFailAlloc_3457_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3456_ = lean_array_push(v_result_3415_, v___x_3455_);
                return v___x_3456_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___boxed(
    mut v___x_3462_: *mut LeanObject,
    mut v_a_3463_: *mut LeanObject,
    mut v_params_3464_: *mut LeanObject,
    mut v___ctx_3465_: *mut LeanObject,
    mut v_info_3466_: *mut LeanObject,
    mut v_result_3467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3468_: *mut LeanObject = core::ptr::null_mut();
    v_res_3468_ =
        l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0(
            v___x_3462_,
            v_a_3463_,
            v_params_3464_,
            v___ctx_3465_,
            v_info_3466_,
            v_result_3467_,
        );
    lean_dec_ref(v_info_3466_);
    lean_dec_ref(v___ctx_3465_);
    lean_dec_ref(v_params_3464_);
    lean_dec(v___x_3462_);
    return v_res_3468_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider(
    mut v_params_3471_: *mut LeanObject,
    mut v_snap_3472_: *mut LeanObject,
    mut v_a_3473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3479_: u8 = 0;
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3475_ = l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(v_a_3473_);
                v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
                v_isSharedCheck_3488_ = (!lean_is_exclusive(v___x_3475_)) as u8;
                if v_isSharedCheck_3488_ == 0 {
                    v___x_3478_ = v___x_3475_;
                    v_isShared_3479_ = v_isSharedCheck_3488_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3476_);
                    lean_dec(v___x_3475_);
                    v___x_3478_ = lean_box(0);
                    v_isShared_3479_ = v_isSharedCheck_3488_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3480_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
                v___f_3481_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___f_3481_, 0, v___x_3480_);
                lean_closure_set(v___f_3481_, 1, v_a_3476_);
                lean_closure_set(v___f_3481_, 2, v_params_3471_);
                v___x_3482_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___closed__0;
                v___x_3483_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_3472_);
                v___x_3484_ =
                    l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_3481_, v___x_3482_, v___x_3483_);
                if v_isShared_3479_ == 0 {
                    lean_ctor_set(v___x_3478_, 0, v___x_3484_);
                    v___x_3486_ = v___x_3478_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
                    v___x_3486_ = v_reuseFailAlloc_3487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___boxed(
    mut v_params_3489_: *mut LeanObject,
    mut v_snap_3490_: *mut LeanObject,
    mut v_a_3491_: *mut LeanObject,
    mut v_a_3492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3493_: *mut LeanObject = core::ptr::null_mut();
    v_res_3493_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider(
        v_params_3489_,
        v_snap_3490_,
        v_a_3491_,
    );
    lean_dec_ref(v_a_3491_);
    return v_res_3493_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1()
-> *mut LeanObject {
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    v___x_3532_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__14;
    v___x_3533_ = lean_alloc_closure(
        l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___boxed
            as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_3534_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_3532_, v___x_3533_);
    return v___x_3534_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___boxed(
    mut v_a_3535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3536_: *mut LeanObject = core::ptr::null_mut();
    v_res_3536_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1();
    return v_res_3536_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(
    mut v_opts_3537_: *mut LeanObject,
    mut v_opt_3538_: *mut LeanObject,
) -> u8 {
    let mut v_name_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    v_name_3539_ = lean_ctor_get(v_opt_3538_, 0);
    v_defValue_3540_ = lean_ctor_get(v_opt_3538_, 1);
    v_map_3541_ = lean_ctor_get(v_opts_3537_, 0);
    v___x_3542_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3541_,
            v_name_3539_,
        );
    if lean_obj_tag(v___x_3542_) == 0 {
        let mut v___x_3543_: u8 = 0;
        v___x_3543_ = (lean_unbox(v_defValue_3540_) as u8);
        return v___x_3543_;
    } else {
        let mut v_val_3544_: *mut LeanObject = core::ptr::null_mut();
        v_val_3544_ = lean_ctor_get(v___x_3542_, 0);
        lean_inc(v_val_3544_);
        lean_dec_ref_known(v___x_3542_, 1);
        if lean_obj_tag(v_val_3544_) == 1 {
            let mut v_v_3545_: u8 = 0;
            v_v_3545_ = lean_ctor_get_uint8(v_val_3544_, 0 as u32);
            lean_dec_ref_known(v_val_3544_, 0);
            return v_v_3545_;
        } else {
            let mut v___x_3546_: u8 = 0;
            lean_dec(v_val_3544_);
            v___x_3546_ = (lean_unbox(v_defValue_3540_) as u8);
            return v___x_3546_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1___boxed(
    mut v_opts_3547_: *mut LeanObject,
    mut v_opt_3548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3549_: u8 = 0;
    let mut v_r_3550_: *mut LeanObject = core::ptr::null_mut();
    v_res_3549_ =
        l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(
            v_opts_3547_,
            v_opt_3548_,
        );
    lean_dec_ref(v_opt_3548_);
    lean_dec_ref(v_opts_3547_);
    v_r_3550_ = lean_box((v_res_3549_) as usize);
    return v_r_3550_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(
    mut v_opts_3551_: *mut LeanObject,
    mut v_opt_3552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    v_name_3553_ = lean_ctor_get(v_opt_3552_, 0);
    v_defValue_3554_ = lean_ctor_get(v_opt_3552_, 1);
    v_map_3555_ = lean_ctor_get(v_opts_3551_, 0);
    v___x_3556_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3555_,
            v_name_3553_,
        );
    if lean_obj_tag(v___x_3556_) == 0 {
        lean_inc(v_defValue_3554_);
        return v_defValue_3554_;
    } else {
        let mut v_val_3557_: *mut LeanObject = core::ptr::null_mut();
        v_val_3557_ = lean_ctor_get(v___x_3556_, 0);
        lean_inc(v_val_3557_);
        lean_dec_ref_known(v___x_3556_, 1);
        if lean_obj_tag(v_val_3557_) == 3 {
            let mut v_v_3558_: *mut LeanObject = core::ptr::null_mut();
            v_v_3558_ = lean_ctor_get(v_val_3557_, 0);
            lean_inc(v_v_3558_);
            lean_dec_ref_known(v_val_3557_, 1);
            return v_v_3558_;
        } else {
            lean_dec(v_val_3557_);
            lean_inc(v_defValue_3554_);
            return v_defValue_3554_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2___boxed(
    mut v_opts_3559_: *mut LeanObject,
    mut v_opt_3560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3561_: *mut LeanObject = core::ptr::null_mut();
    v_res_3561_ =
        l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(
            v_opts_3559_,
            v_opt_3560_,
        );
    lean_dec_ref(v_opt_3560_);
    lean_dec_ref(v_opts_3559_);
    return v_res_3561_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0(
    mut v_o_3565_: *mut LeanObject,
    mut v_k_3566_: *mut LeanObject,
    mut v_v_3567_: u8,
) -> *mut LeanObject {
    let mut v_map_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3569_: u8 = 0;
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3572_: u8 = 0;
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: u8 = 0;
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3568_ = lean_ctor_get(v_o_3565_, 0);
                v_hasTrace_3569_ = lean_ctor_get_uint8(
                    v_o_3565_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3583_ = (!lean_is_exclusive(v_o_3565_)) as u8;
                if v_isSharedCheck_3583_ == 0 {
                    v___x_3571_ = v_o_3565_;
                    v_isShared_3572_ = v_isSharedCheck_3583_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_3568_);
                    lean_dec(v_o_3565_);
                    v___x_3571_ = lean_box(0);
                    v_isShared_3572_ = v_isSharedCheck_3583_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3573_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_3573_, 0 as u32, v_v_3567_);
                lean_inc(v_k_3566_);
                v___x_3574_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3566_, v___x_3573_, v_map_3568_);
                if v_hasTrace_3569_ == 0 {
                    v___x_3575_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__1;
                    v___x_3576_ = l_Lean_Name_isPrefixOf(v___x_3575_, v_k_3566_);
                    lean_dec(v_k_3566_);
                    if v_isShared_3572_ == 0 {
                        lean_ctor_set(v___x_3571_, 0, v___x_3574_);
                        v___x_3578_ = v___x_3571_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3574_);
                        v___x_3578_ = v_reuseFailAlloc_3579_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_3566_);
                    if v_isShared_3572_ == 0 {
                        lean_ctor_set(v___x_3571_, 0, v___x_3574_);
                        v___x_3581_ = v___x_3571_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3574_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_3582_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_3569_,
                        );
                        v___x_3581_ = v_reuseFailAlloc_3582_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_3578_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3576_,
                );
                return v___x_3578_;
            }
            3 => {
                return v___x_3581_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___boxed(
    mut v_o_3584_: *mut LeanObject,
    mut v_k_3585_: *mut LeanObject,
    mut v_v_3586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_3587_: u8 = 0;
    let mut v_res_3588_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_3587_ = (lean_unbox(v_v_3586_) as u8);
    v_res_3588_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0(v_o_3584_, v_k_3585_, v_v_boxed_3587_);
    return v_res_3588_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(
    mut v_opts_3589_: *mut LeanObject,
    mut v_opt_3590_: *mut LeanObject,
    mut v_val_3591_: u8,
) -> *mut LeanObject {
    let mut v_name_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    v_name_3592_ = lean_ctor_get(v_opt_3590_, 0);
    lean_inc(v_name_3592_);
    lean_dec_ref(v_opt_3590_);
    v___x_3593_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0(v_opts_3589_, v_name_3592_, v_val_3591_);
    return v___x_3593_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0___boxed(
    mut v_opts_3594_: *mut LeanObject,
    mut v_opt_3595_: *mut LeanObject,
    mut v_val_3596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_3597_: u8 = 0;
    let mut v_res_3598_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_3597_ = (lean_unbox(v_val_3596_) as u8);
    v_res_3598_ =
        l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(
            v_opts_3594_,
            v_opt_3595_,
            v_val_boxed_3597_,
        );
    return v_res_3598_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0()
-> *mut LeanObject {
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    v___x_3599_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3599_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1()
-> *mut LeanObject {
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    v___x_3600_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0_once),
        _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0,
    );
    v___x_3601_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3601_, 0, v___x_3600_);
    return v___x_3601_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2()
-> *mut LeanObject {
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    v___x_3602_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1_once),
        _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1,
    );
    v___x_3603_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3603_, 0, v___x_3602_);
    lean_ctor_set(v___x_3603_, 1, v___x_3602_);
    return v___x_3603_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(
    mut v_e_3604_: *mut LeanObject,
    mut v_a_3605_: *mut LeanObject,
    mut v_a_3606_: *mut LeanObject,
    mut v_a_3607_: *mut LeanObject,
    mut v_a_3608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3623_: u8 = 0;
    let mut v_inheritedTraceOptions_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: u8 = 0;
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: u8 = 0;
    let mut v_fileName_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3644_: u8 = 0;
    let mut v_inheritedTraceOptions_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3652_: u8 = 0;
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3664_: u8 = 0;
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut v_unused_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3610_ = lean_st_ref_get(v_a_3608_);
                v_fileName_3611_ = lean_ctor_get(v_a_3607_, 0);
                v_fileMap_3612_ = lean_ctor_get(v_a_3607_, 1);
                v_options_3613_ = lean_ctor_get(v_a_3607_, 2);
                v_currRecDepth_3614_ = lean_ctor_get(v_a_3607_, 3);
                v_ref_3615_ = lean_ctor_get(v_a_3607_, 5);
                v_currNamespace_3616_ = lean_ctor_get(v_a_3607_, 6);
                v_openDecls_3617_ = lean_ctor_get(v_a_3607_, 7);
                v_initHeartbeats_3618_ = lean_ctor_get(v_a_3607_, 8);
                v_maxHeartbeats_3619_ = lean_ctor_get(v_a_3607_, 9);
                v_quotContext_3620_ = lean_ctor_get(v_a_3607_, 10);
                v_currMacroScope_3621_ = lean_ctor_get(v_a_3607_, 11);
                v_cancelTk_x3f_3622_ = lean_ctor_get(v_a_3607_, 12);
                v_suppressElabErrors_3623_ = lean_ctor_get_uint8(
                    v_a_3607_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3624_ = lean_ctor_get(v_a_3607_, 13);
                v_env_3625_ = lean_ctor_get(v___x_3610_, 0);
                lean_inc_ref(v_env_3625_);
                lean_dec(v___x_3610_);
                v___x_3626_ = lean_box(1);
                v___x_3627_ = l_Lean_pp_mvars_anonymous;
                v___x_3628_ = 0;
                lean_inc_ref(v_options_3613_);
                v___x_3629_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_options_3613_, v___x_3627_, v___x_3628_);
                v___x_3630_ = l_Lean_diagnostics;
                v___x_3631_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v___x_3629_, v___x_3630_);
                v___x_3673_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3625_);
                lean_dec_ref(v_env_3625_);
                if v___x_3673_ == 0 {
                    if v___x_3631_ == 0 {
                        v_fileName_3633_ = v_fileName_3611_;
                        v_fileMap_3634_ = v_fileMap_3612_;
                        v_currRecDepth_3635_ = v_currRecDepth_3614_;
                        v_ref_3636_ = v_ref_3615_;
                        v_currNamespace_3637_ = v_currNamespace_3616_;
                        v_openDecls_3638_ = v_openDecls_3617_;
                        v_initHeartbeats_3639_ = v_initHeartbeats_3618_;
                        v_maxHeartbeats_3640_ = v_maxHeartbeats_3619_;
                        v_quotContext_3641_ = v_quotContext_3620_;
                        v_currMacroScope_3642_ = v_currMacroScope_3621_;
                        v_cancelTk_x3f_3643_ = v_cancelTk_x3f_3622_;
                        v_suppressElabErrors_3644_ = v_suppressElabErrors_3623_;
                        v_inheritedTraceOptions_3645_ = v_inheritedTraceOptions_3624_;
                        v___y_3646_ = v_a_3608_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3652_ = v___x_3673_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___y_3652_ = v___x_3631_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3647_ = l_Lean_maxRecDepth;
                v___x_3648_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(v___x_3629_, v___x_3647_);
                lean_inc_ref(v_inheritedTraceOptions_3645_);
                lean_inc(v_cancelTk_x3f_3643_);
                lean_inc(v_currMacroScope_3642_);
                lean_inc(v_quotContext_3641_);
                lean_inc(v_maxHeartbeats_3640_);
                lean_inc(v_initHeartbeats_3639_);
                lean_inc(v_openDecls_3638_);
                lean_inc(v_currNamespace_3637_);
                lean_inc(v_ref_3636_);
                lean_inc(v_currRecDepth_3635_);
                lean_inc_ref(v_fileMap_3634_);
                lean_inc_ref(v_fileName_3633_);
                v___x_3649_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_3649_, 0, v_fileName_3633_);
                lean_ctor_set(v___x_3649_, 1, v_fileMap_3634_);
                lean_ctor_set(v___x_3649_, 2, v___x_3629_);
                lean_ctor_set(v___x_3649_, 3, v_currRecDepth_3635_);
                lean_ctor_set(v___x_3649_, 4, v___x_3648_);
                lean_ctor_set(v___x_3649_, 5, v_ref_3636_);
                lean_ctor_set(v___x_3649_, 6, v_currNamespace_3637_);
                lean_ctor_set(v___x_3649_, 7, v_openDecls_3638_);
                lean_ctor_set(v___x_3649_, 8, v_initHeartbeats_3639_);
                lean_ctor_set(v___x_3649_, 9, v_maxHeartbeats_3640_);
                lean_ctor_set(v___x_3649_, 10, v_quotContext_3641_);
                lean_ctor_set(v___x_3649_, 11, v_currMacroScope_3642_);
                lean_ctor_set(v___x_3649_, 12, v_cancelTk_x3f_3643_);
                lean_ctor_set(v___x_3649_, 13, v_inheritedTraceOptions_3645_);
                lean_ctor_set_uint8(
                    v___x_3649_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_3631_,
                );
                lean_ctor_set_uint8(
                    v___x_3649_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3644_,
                );
                v___x_3650_ = l_Lean_PrettyPrinter_delab(
                    v_e_3604_,
                    v___x_3626_,
                    v_a_3605_,
                    v_a_3606_,
                    v___x_3649_,
                    v___y_3646_,
                );
                lean_dec_ref_known(v___x_3649_, 14);
                return v___x_3650_;
            }
            2 => {
                if v___y_3652_ == 0 {
                    v___x_3653_ = lean_st_ref_take(v_a_3608_);
                    v_env_3654_ = lean_ctor_get(v___x_3653_, 0);
                    v_nextMacroScope_3655_ = lean_ctor_get(v___x_3653_, 1);
                    v_ngen_3656_ = lean_ctor_get(v___x_3653_, 2);
                    v_auxDeclNGen_3657_ = lean_ctor_get(v___x_3653_, 3);
                    v_traceState_3658_ = lean_ctor_get(v___x_3653_, 4);
                    v_messages_3659_ = lean_ctor_get(v___x_3653_, 6);
                    v_infoState_3660_ = lean_ctor_get(v___x_3653_, 7);
                    v_snapshotTasks_3661_ = lean_ctor_get(v___x_3653_, 8);
                    v_isSharedCheck_3671_ = (!lean_is_exclusive(v___x_3653_)) as u8;
                    if v_isSharedCheck_3671_ == 0 {
                        v_unused_3672_ = lean_ctor_get(v___x_3653_, 5);
                        lean_dec(v_unused_3672_);
                        v___x_3663_ = v___x_3653_;
                        v_isShared_3664_ = v_isSharedCheck_3671_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_3661_);
                        lean_inc(v_infoState_3660_);
                        lean_inc(v_messages_3659_);
                        lean_inc(v_traceState_3658_);
                        lean_inc(v_auxDeclNGen_3657_);
                        lean_inc(v_ngen_3656_);
                        lean_inc(v_nextMacroScope_3655_);
                        lean_inc(v_env_3654_);
                        lean_dec(v___x_3653_);
                        v___x_3663_ = lean_box(0);
                        v_isShared_3664_ = v_isSharedCheck_3671_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_fileName_3633_ = v_fileName_3611_;
                    v_fileMap_3634_ = v_fileMap_3612_;
                    v_currRecDepth_3635_ = v_currRecDepth_3614_;
                    v_ref_3636_ = v_ref_3615_;
                    v_currNamespace_3637_ = v_currNamespace_3616_;
                    v_openDecls_3638_ = v_openDecls_3617_;
                    v_initHeartbeats_3639_ = v_initHeartbeats_3618_;
                    v_maxHeartbeats_3640_ = v_maxHeartbeats_3619_;
                    v_quotContext_3641_ = v_quotContext_3620_;
                    v_currMacroScope_3642_ = v_currMacroScope_3621_;
                    v_cancelTk_x3f_3643_ = v_cancelTk_x3f_3622_;
                    v_suppressElabErrors_3644_ = v_suppressElabErrors_3623_;
                    v_inheritedTraceOptions_3645_ = v_inheritedTraceOptions_3624_;
                    v___y_3646_ = v_a_3608_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3665_ = l_Lean_Kernel_enableDiag(v_env_3654_, v___x_3631_);
                v___x_3666_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2,
                );
                if v_isShared_3664_ == 0 {
                    lean_ctor_set(v___x_3663_, 5, v___x_3666_);
                    lean_ctor_set(v___x_3663_, 0, v___x_3665_);
                    v___x_3668_ = v___x_3663_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3665_);
                    lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_nextMacroScope_3655_);
                    lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_ngen_3656_);
                    lean_ctor_set(v_reuseFailAlloc_3670_, 3, v_auxDeclNGen_3657_);
                    lean_ctor_set(v_reuseFailAlloc_3670_, 4, v_traceState_3658_);
                    lean_ctor_set(v_reuseFailAlloc_3670_, 5, v___x_3666_);
                    lean_ctor_set(v_reuseFailAlloc_3670_, 6, v_messages_3659_);
                    lean_ctor_set(v_reuseFailAlloc_3670_, 7, v_infoState_3660_);
                    lean_ctor_set(v_reuseFailAlloc_3670_, 8, v_snapshotTasks_3661_);
                    v___x_3668_ = v_reuseFailAlloc_3670_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3669_ = lean_st_ref_set(v_a_3608_, v___x_3668_);
                v_fileName_3633_ = v_fileName_3611_;
                v_fileMap_3634_ = v_fileMap_3612_;
                v_currRecDepth_3635_ = v_currRecDepth_3614_;
                v_ref_3636_ = v_ref_3615_;
                v_currNamespace_3637_ = v_currNamespace_3616_;
                v_openDecls_3638_ = v_openDecls_3617_;
                v_initHeartbeats_3639_ = v_initHeartbeats_3618_;
                v_maxHeartbeats_3640_ = v_maxHeartbeats_3619_;
                v_quotContext_3641_ = v_quotContext_3620_;
                v_currMacroScope_3642_ = v_currMacroScope_3621_;
                v_cancelTk_x3f_3643_ = v_cancelTk_x3f_3622_;
                v_suppressElabErrors_3644_ = v_suppressElabErrors_3623_;
                v_inheritedTraceOptions_3645_ = v_inheritedTraceOptions_3624_;
                v___y_3646_ = v_a_3608_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___boxed(
    mut v_e_3674_: *mut LeanObject,
    mut v_a_3675_: *mut LeanObject,
    mut v_a_3676_: *mut LeanObject,
    mut v_a_3677_: *mut LeanObject,
    mut v_a_3678_: *mut LeanObject,
    mut v_a_3679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3680_: *mut LeanObject = core::ptr::null_mut();
    v_res_3680_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(
        v_e_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_,
    );
    lean_dec(v_a_3678_);
    lean_dec_ref(v_a_3677_);
    lean_dec(v_a_3676_);
    lean_dec_ref(v_a_3675_);
    return v_res_3680_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(
    mut v_msgData_3681_: *mut LeanObject,
    mut v___y_3682_: *mut LeanObject,
    mut v___y_3683_: *mut LeanObject,
    mut v___y_3684_: *mut LeanObject,
    mut v___y_3685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    v___x_3687_ = lean_st_ref_get(v___y_3685_);
    v_env_3688_ = lean_ctor_get(v___x_3687_, 0);
    lean_inc_ref(v_env_3688_);
    lean_dec(v___x_3687_);
    v___x_3689_ = lean_st_ref_get(v___y_3683_);
    v_mctx_3690_ = lean_ctor_get(v___x_3689_, 0);
    lean_inc_ref(v_mctx_3690_);
    lean_dec(v___x_3689_);
    v_lctx_3691_ = lean_ctor_get(v___y_3682_, 2);
    v_options_3692_ = lean_ctor_get(v___y_3684_, 2);
    lean_inc_ref(v_options_3692_);
    lean_inc_ref(v_lctx_3691_);
    v___x_3693_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3693_, 0, v_env_3688_);
    lean_ctor_set(v___x_3693_, 1, v_mctx_3690_);
    lean_ctor_set(v___x_3693_, 2, v_lctx_3691_);
    lean_ctor_set(v___x_3693_, 3, v_options_3692_);
    v___x_3694_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3694_, 0, v___x_3693_);
    lean_ctor_set(v___x_3694_, 1, v_msgData_3681_);
    v___x_3695_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3695_, 0, v___x_3694_);
    return v___x_3695_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0___boxed(
    mut v_msgData_3696_: *mut LeanObject,
    mut v___y_3697_: *mut LeanObject,
    mut v___y_3698_: *mut LeanObject,
    mut v___y_3699_: *mut LeanObject,
    mut v___y_3700_: *mut LeanObject,
    mut v___y_3701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3702_: *mut LeanObject = core::ptr::null_mut();
    v_res_3702_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_msgData_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
    lean_dec(v___y_3700_);
    lean_dec_ref(v___y_3699_);
    lean_dec(v___y_3698_);
    lean_dec_ref(v___y_3697_);
    return v_res_3702_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(
    mut v_e_3706_: *mut LeanObject,
    mut v_a_3707_: *mut LeanObject,
    mut v_a_3708_: *mut LeanObject,
    mut v_a_3709_: *mut LeanObject,
    mut v_a_3710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3719_: u8 = 0;
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut v_a_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3732_: u8 = 0;
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_3706_);
                v___x_3712_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(
                    v_e_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_,
                );
                if lean_obj_tag(v___x_3712_) == 0 {
                    v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
                    lean_inc(v_a_3713_);
                    lean_dec_ref_known(v___x_3712_, 1);
                    v___x_3714_ = l_Lean_MessageData_ofExpr(v_e_3706_);
                    v___x_3715_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_3714_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
                    v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
                    v_isSharedCheck_3728_ = (!lean_is_exclusive(v___x_3715_)) as u8;
                    if v_isSharedCheck_3728_ == 0 {
                        v___x_3718_ = v___x_3715_;
                        v_isShared_3719_ = v_isSharedCheck_3728_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3716_);
                        lean_dec(v___x_3715_);
                        v___x_3718_ = lean_box(0);
                        v_isShared_3719_ = v_isSharedCheck_3728_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3706_);
                    v_a_3729_ = lean_ctor_get(v___x_3712_, 0);
                    v_isSharedCheck_3736_ = (!lean_is_exclusive(v___x_3712_)) as u8;
                    if v_isSharedCheck_3736_ == 0 {
                        v___x_3731_ = v___x_3712_;
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3729_);
                        lean_dec(v___x_3712_);
                        v___x_3731_ = lean_box(0);
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3720_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1;
                v___x_3721_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3721_, 0, v___x_3720_);
                lean_ctor_set(v___x_3721_, 1, v_a_3713_);
                v___x_3722_ = lean_box(0);
                v___x_3723_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3723_, 0, v_a_3716_);
                v___x_3724_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_3724_, 0, v___x_3721_);
                lean_ctor_set(v___x_3724_, 1, v___x_3722_);
                lean_ctor_set(v___x_3724_, 2, v___x_3722_);
                lean_ctor_set(v___x_3724_, 3, v___x_3722_);
                lean_ctor_set(v___x_3724_, 4, v___x_3723_);
                lean_ctor_set(v___x_3724_, 5, v___x_3722_);
                if v_isShared_3719_ == 0 {
                    lean_ctor_set(v___x_3718_, 0, v___x_3724_);
                    v___x_3726_ = v___x_3718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3724_);
                    v___x_3726_ = v_reuseFailAlloc_3727_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3726_;
            }
            3 => {
                if v_isShared_3732_ == 0 {
                    v___x_3734_ = v___x_3731_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
                    v___x_3734_ = v_reuseFailAlloc_3735_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___boxed(
    mut v_e_3737_: *mut LeanObject,
    mut v_a_3738_: *mut LeanObject,
    mut v_a_3739_: *mut LeanObject,
    mut v_a_3740_: *mut LeanObject,
    mut v_a_3741_: *mut LeanObject,
    mut v_a_3742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3743_: *mut LeanObject = core::ptr::null_mut();
    v_res_3743_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(
        v_e_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_,
    );
    lean_dec(v_a_3741_);
    lean_dec_ref(v_a_3740_);
    lean_dec(v_a_3739_);
    lean_dec_ref(v_a_3738_);
    return v_res_3743_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    v___x_3744_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3744_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    v___x_3745_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0);
    v___x_3746_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3746_, 0, v___x_3745_);
    return v___x_3746_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    v___x_3747_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1);
    v___x_3748_ = lean_unsigned_to_nat(0);
    v___x_3749_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3749_, 0, v___x_3748_);
    lean_ctor_set(v___x_3749_, 1, v___x_3748_);
    lean_ctor_set(v___x_3749_, 2, v___x_3748_);
    lean_ctor_set(v___x_3749_, 3, v___x_3748_);
    lean_ctor_set(v___x_3749_, 4, v___x_3747_);
    lean_ctor_set(v___x_3749_, 5, v___x_3747_);
    lean_ctor_set(v___x_3749_, 6, v___x_3747_);
    lean_ctor_set(v___x_3749_, 7, v___x_3747_);
    lean_ctor_set(v___x_3749_, 8, v___x_3747_);
    lean_ctor_set(v___x_3749_, 9, v___x_3747_);
    return v___x_3749_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    v___x_3750_ = lean_unsigned_to_nat(32);
    v___x_3751_ = lean_mk_empty_array_with_capacity(v___x_3750_);
    v___x_3752_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3752_, 0, v___x_3751_);
    return v___x_3752_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4()
-> *mut LeanObject {
    let mut v___x_3753_: usize = 0;
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    v___x_3753_ = 5usize;
    v___x_3754_ = lean_unsigned_to_nat(0);
    v___x_3755_ = lean_unsigned_to_nat(32);
    v___x_3756_ = lean_mk_empty_array_with_capacity(v___x_3755_);
    v___x_3757_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3);
    v___x_3758_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3758_, 0, v___x_3757_);
    lean_ctor_set(v___x_3758_, 1, v___x_3756_);
    lean_ctor_set(v___x_3758_, 2, v___x_3754_);
    lean_ctor_set(v___x_3758_, 3, v___x_3754_);
    lean_ctor_set_usize(v___x_3758_, 4, v___x_3753_);
    return v___x_3758_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    v___x_3759_ = lean_box(1);
    v___x_3760_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4);
    v___x_3761_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1);
    v___x_3762_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3762_, 0, v___x_3761_);
    lean_ctor_set(v___x_3762_, 1, v___x_3760_);
    lean_ctor_set(v___x_3762_, 2, v___x_3759_);
    return v___x_3762_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(
    mut v_msgData_3763_: *mut LeanObject,
    mut v___y_3764_: *mut LeanObject,
    mut v___y_3765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    v___x_3767_ = lean_st_ref_get(v___y_3765_);
    v_env_3768_ = lean_ctor_get(v___x_3767_, 0);
    lean_inc_ref(v_env_3768_);
    lean_dec(v___x_3767_);
    v_options_3769_ = lean_ctor_get(v___y_3764_, 2);
    v___x_3770_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2);
    v___x_3771_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5);
    lean_inc_ref(v_options_3769_);
    v___x_3772_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3772_, 0, v_env_3768_);
    lean_ctor_set(v___x_3772_, 1, v___x_3770_);
    lean_ctor_set(v___x_3772_, 2, v___x_3771_);
    lean_ctor_set(v___x_3772_, 3, v_options_3769_);
    v___x_3773_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3773_, 0, v___x_3772_);
    lean_ctor_set(v___x_3773_, 1, v_msgData_3763_);
    v___x_3774_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3774_, 0, v___x_3773_);
    return v___x_3774_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_3775_: *mut LeanObject,
    mut v___y_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3779_: *mut LeanObject = core::ptr::null_mut();
    v_res_3779_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v_msgData_3775_, v___y_3776_, v___y_3777_);
    lean_dec(v___y_3777_);
    lean_dec_ref(v___y_3776_);
    return v_res_3779_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(
    mut v___y_3786_: u8,
    mut v_suppressElabErrors_3787_: u8,
    mut v_x_3788_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_3788_) == 1 {
        let mut v_pre_3789_: *mut LeanObject = core::ptr::null_mut();
        v_pre_3789_ = lean_ctor_get(v_x_3788_, 0);
        match lean_obj_tag(v_pre_3789_) {
            1 => {
                let mut v_pre_3790_: *mut LeanObject = core::ptr::null_mut();
                v_pre_3790_ = lean_ctor_get(v_pre_3789_, 0);
                match lean_obj_tag(v_pre_3790_) {
                    0 => {
                        let mut v_str_3791_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_3792_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3794_: u8 = 0;
                        v_str_3791_ = lean_ctor_get(v_x_3788_, 1);
                        v_str_3792_ = lean_ctor_get(v_pre_3789_, 1);
                        v___x_3793_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0;
                        v___x_3794_ = lean_string_dec_eq(v_str_3792_, v___x_3793_);
                        if v___x_3794_ == 0 {
                            let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3796_: u8 = 0;
                            v___x_3795_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4;
                            v___x_3796_ = lean_string_dec_eq(v_str_3792_, v___x_3795_);
                            if v___x_3796_ == 0 {
                                return v___y_3786_;
                            } else {
                                let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_3798_: u8 = 0;
                                v___x_3797_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__1;
                                v___x_3798_ = lean_string_dec_eq(v_str_3791_, v___x_3797_);
                                if v___x_3798_ == 0 {
                                    return v___y_3786_;
                                } else {
                                    return v_suppressElabErrors_3787_;
                                }
                            }
                        } else {
                            let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3800_: u8 = 0;
                            v___x_3799_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__2;
                            v___x_3800_ = lean_string_dec_eq(v_str_3791_, v___x_3799_);
                            if v___x_3800_ == 0 {
                                return v___y_3786_;
                            } else {
                                return v_suppressElabErrors_3787_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_3801_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_3801_ = lean_ctor_get(v_pre_3790_, 0);
                        if lean_obj_tag(v_pre_3801_) == 0 {
                            let mut v_str_3802_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_3803_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_3804_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3806_: u8 = 0;
                            v_str_3802_ = lean_ctor_get(v_x_3788_, 1);
                            v_str_3803_ = lean_ctor_get(v_pre_3789_, 1);
                            v_str_3804_ = lean_ctor_get(v_pre_3790_, 1);
                            v___x_3805_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__3;
                            v___x_3806_ = lean_string_dec_eq(v_str_3804_, v___x_3805_);
                            if v___x_3806_ == 0 {
                                return v___y_3786_;
                            } else {
                                let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_3808_: u8 = 0;
                                v___x_3807_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__4;
                                v___x_3808_ = lean_string_dec_eq(v_str_3803_, v___x_3807_);
                                if v___x_3808_ == 0 {
                                    return v___y_3786_;
                                } else {
                                    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_3810_: u8 = 0;
                                    v___x_3809_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__5;
                                    v___x_3810_ = lean_string_dec_eq(v_str_3802_, v___x_3809_);
                                    if v___x_3810_ == 0 {
                                        return v___y_3786_;
                                    } else {
                                        return v_suppressElabErrors_3787_;
                                    }
                                }
                            }
                        } else {
                            return v___y_3786_;
                        }
                    }
                    _ => {
                        return v___y_3786_;
                    }
                }
            }
            0 => {
                let mut v_str_3811_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3813_: u8 = 0;
                v_str_3811_ = lean_ctor_get(v_x_3788_, 1);
                v___x_3812_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__0;
                v___x_3813_ = lean_string_dec_eq(v_str_3811_, v___x_3812_);
                if v___x_3813_ == 0 {
                    return v___y_3786_;
                } else {
                    return v_suppressElabErrors_3787_;
                }
            }
            _ => {
                return v___y_3786_;
            }
        }
    } else {
        return v___y_3786_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed(
    mut v___y_3814_: *mut LeanObject,
    mut v_suppressElabErrors_3815_: *mut LeanObject,
    mut v_x_3816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2411__boxed_3817_: u8 = 0;
    let mut v_suppressElabErrors_boxed_3818_: u8 = 0;
    let mut v_res_3819_: u8 = 0;
    let mut v_r_3820_: *mut LeanObject = core::ptr::null_mut();
    v___y_2411__boxed_3817_ = (lean_unbox(v___y_3814_) as u8);
    v_suppressElabErrors_boxed_3818_ = (lean_unbox(v_suppressElabErrors_3815_) as u8);
    v_res_3819_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(v___y_2411__boxed_3817_, v_suppressElabErrors_boxed_3818_, v_x_3816_);
    lean_dec(v_x_3816_);
    v_r_3820_ = lean_box((v_res_3819_) as usize);
    return v_r_3820_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(
    mut v_ref_3822_: *mut LeanObject,
    mut v_msgData_3823_: *mut LeanObject,
    mut v_severity_3824_: u8,
    mut v_isSilent_3825_: u8,
    mut v___y_3826_: *mut LeanObject,
    mut v___y_3827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3831_: u8 = 0;
    let mut v___y_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3834_: u8 = 0;
    let mut v___y_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3853_: u8 = 0;
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3864_: u8 = 0;
    let mut v___y_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3867_: u8 = 0;
    let mut v___y_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3869_: u8 = 0;
    let mut v___y_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3872_: u8 = 0;
    let mut v___y_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: u8 = 0;
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3889_: u8 = 0;
    let mut v___y_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: u8 = 0;
    let mut v___y_3893_: u8 = 0;
    let mut v___y_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3897_: u8 = 0;
    let mut v___y_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3903_: u8 = 0;
    let mut v___y_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: u8 = 0;
    let mut v___y_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: u8 = 0;
    let mut v_ref_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: u8 = 0;
    let mut v___y_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3916_: u8 = 0;
    let mut v___y_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3920_: u8 = 0;
    let mut v___y_3921_: u8 = 0;
    let mut v___y_3923_: u8 = 0;
    let mut v_fileName_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3928_: u8 = 0;
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: u8 = 0;
    let mut v___x_3933_: u8 = 0;
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: u8 = 0;
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: u8 = 0;
    let mut v___x_3939_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3913_ = 2;
                v___x_3938_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3824_, v___x_3913_);
                if v___x_3938_ == 0 {
                    v___y_3923_ = v___x_3938_;
                    state = 10;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_3823_);
                    v___x_3939_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3823_);
                    v___y_3923_ = v___x_3939_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_3839_ = lean_st_ref_take(v___y_3838_);
                v_currNamespace_3840_ = lean_ctor_get(v___y_3837_, 6);
                v_openDecls_3841_ = lean_ctor_get(v___y_3837_, 7);
                v_env_3842_ = lean_ctor_get(v___x_3839_, 0);
                v_nextMacroScope_3843_ = lean_ctor_get(v___x_3839_, 1);
                v_ngen_3844_ = lean_ctor_get(v___x_3839_, 2);
                v_auxDeclNGen_3845_ = lean_ctor_get(v___x_3839_, 3);
                v_traceState_3846_ = lean_ctor_get(v___x_3839_, 4);
                v_cache_3847_ = lean_ctor_get(v___x_3839_, 5);
                v_messages_3848_ = lean_ctor_get(v___x_3839_, 6);
                v_infoState_3849_ = lean_ctor_get(v___x_3839_, 7);
                v_snapshotTasks_3850_ = lean_ctor_get(v___x_3839_, 8);
                v_isSharedCheck_3864_ = (!lean_is_exclusive(v___x_3839_)) as u8;
                if v_isSharedCheck_3864_ == 0 {
                    v___x_3852_ = v___x_3839_;
                    v_isShared_3853_ = v_isSharedCheck_3864_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3850_);
                    lean_inc(v_infoState_3849_);
                    lean_inc(v_messages_3848_);
                    lean_inc(v_cache_3847_);
                    lean_inc(v_traceState_3846_);
                    lean_inc(v_auxDeclNGen_3845_);
                    lean_inc(v_ngen_3844_);
                    lean_inc(v_nextMacroScope_3843_);
                    lean_inc(v_env_3842_);
                    lean_dec(v___x_3839_);
                    v___x_3852_ = lean_box(0);
                    v_isShared_3853_ = v_isSharedCheck_3864_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_3841_);
                lean_inc(v_currNamespace_3840_);
                v___x_3854_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3854_, 0, v_currNamespace_3840_);
                lean_ctor_set(v___x_3854_, 1, v_openDecls_3841_);
                v___x_3855_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3855_, 0, v___x_3854_);
                lean_ctor_set(v___x_3855_, 1, v___y_3836_);
                lean_inc_ref(v___y_3832_);
                lean_inc_ref(v___y_3833_);
                v___x_3856_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_3856_, 0, v___y_3833_);
                lean_ctor_set(v___x_3856_, 1, v___y_3835_);
                lean_ctor_set(v___x_3856_, 2, v___y_3830_);
                lean_ctor_set(v___x_3856_, 3, v___y_3832_);
                lean_ctor_set(v___x_3856_, 4, v___x_3855_);
                lean_ctor_set_uint8(
                    v___x_3856_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_3834_,
                );
                lean_ctor_set_uint8(
                    v___x_3856_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_3831_,
                );
                lean_ctor_set_uint8(
                    v___x_3856_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_3825_,
                );
                v___x_3857_ = l_Lean_MessageLog_add(v___x_3856_, v_messages_3848_);
                if v_isShared_3853_ == 0 {
                    lean_ctor_set(v___x_3852_, 6, v___x_3857_);
                    v___x_3859_ = v___x_3852_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_env_3842_);
                    lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_nextMacroScope_3843_);
                    lean_ctor_set(v_reuseFailAlloc_3863_, 2, v_ngen_3844_);
                    lean_ctor_set(v_reuseFailAlloc_3863_, 3, v_auxDeclNGen_3845_);
                    lean_ctor_set(v_reuseFailAlloc_3863_, 4, v_traceState_3846_);
                    lean_ctor_set(v_reuseFailAlloc_3863_, 5, v_cache_3847_);
                    lean_ctor_set(v_reuseFailAlloc_3863_, 6, v___x_3857_);
                    lean_ctor_set(v_reuseFailAlloc_3863_, 7, v_infoState_3849_);
                    lean_ctor_set(v_reuseFailAlloc_3863_, 8, v_snapshotTasks_3850_);
                    v___x_3859_ = v_reuseFailAlloc_3863_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3860_ = lean_st_ref_set(v___y_3838_, v___x_3859_);
                v___x_3861_ = lean_box(0);
                v___x_3862_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3862_, 0, v___x_3861_);
                return v___x_3862_;
            }
            4 => {
                v___x_3874_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_3823_,
                    );
                v___x_3875_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v___x_3874_, v___y_3826_, v___y_3827_);
                v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
                v_isSharedCheck_3889_ = (!lean_is_exclusive(v___x_3875_)) as u8;
                if v_isSharedCheck_3889_ == 0 {
                    v___x_3878_ = v___x_3875_;
                    v_isShared_3879_ = v_isSharedCheck_3889_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_3876_);
                    lean_dec(v___x_3875_);
                    v___x_3878_ = lean_box(0);
                    v_isShared_3879_ = v_isSharedCheck_3889_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_3870_, 2);
                v___x_3880_ = l_Lean_FileMap_toPosition(v___y_3870_, v___y_3868_);
                lean_dec(v___y_3868_);
                v___x_3881_ = l_Lean_FileMap_toPosition(v___y_3870_, v___y_3873_);
                lean_dec(v___y_3873_);
                v___x_3882_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3882_, 0, v___x_3881_);
                v___x_3883_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0;
                if v___y_3869_ == 0 {
                    lean_del_object(v___x_3878_);
                    lean_dec_ref(v___y_3866_);
                    v___y_3830_ = v___x_3882_;
                    v___y_3831_ = v___y_3867_;
                    v___y_3832_ = v___x_3883_;
                    v___y_3833_ = v___y_3871_;
                    v___y_3834_ = v___y_3872_;
                    v___y_3835_ = v___x_3880_;
                    v___y_3836_ = v_a_3876_;
                    v___y_3837_ = v___y_3826_;
                    v___y_3838_ = v___y_3827_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3876_);
                    v___x_3884_ = l_Lean_MessageData_hasTag(v___y_3866_, v_a_3876_);
                    if v___x_3884_ == 0 {
                        lean_dec_ref_known(v___x_3882_, 1);
                        lean_dec_ref(v___x_3880_);
                        lean_dec(v_a_3876_);
                        v___x_3885_ = lean_box(0);
                        if v_isShared_3879_ == 0 {
                            lean_ctor_set(v___x_3878_, 0, v___x_3885_);
                            v___x_3887_ = v___x_3878_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
                            v___x_3887_ = v_reuseFailAlloc_3888_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3878_);
                        v___y_3830_ = v___x_3882_;
                        v___y_3831_ = v___y_3867_;
                        v___y_3832_ = v___x_3883_;
                        v___y_3833_ = v___y_3871_;
                        v___y_3834_ = v___y_3872_;
                        v___y_3835_ = v___x_3880_;
                        v___y_3836_ = v_a_3876_;
                        v___y_3837_ = v___y_3826_;
                        v___y_3838_ = v___y_3827_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3887_;
            }
            7 => {
                v___x_3899_ = l_Lean_Syntax_getTailPos_x3f(v___y_3896_, v___y_3897_);
                lean_dec(v___y_3896_);
                if lean_obj_tag(v___x_3899_) == 0 {
                    lean_inc(v___y_3898_);
                    v___y_3866_ = v___y_3891_;
                    v___y_3867_ = v___y_3892_;
                    v___y_3868_ = v___y_3898_;
                    v___y_3869_ = v___y_3893_;
                    v___y_3870_ = v___y_3894_;
                    v___y_3871_ = v___y_3895_;
                    v___y_3872_ = v___y_3897_;
                    v___y_3873_ = v___y_3898_;
                    state = 4;
                    continue;
                } else {
                    v_val_3900_ = lean_ctor_get(v___x_3899_, 0);
                    lean_inc(v_val_3900_);
                    lean_dec_ref_known(v___x_3899_, 1);
                    v___y_3866_ = v___y_3891_;
                    v___y_3867_ = v___y_3892_;
                    v___y_3868_ = v___y_3898_;
                    v___y_3869_ = v___y_3893_;
                    v___y_3870_ = v___y_3894_;
                    v___y_3871_ = v___y_3895_;
                    v___y_3872_ = v___y_3897_;
                    v___y_3873_ = v_val_3900_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_3909_ = l_Lean_replaceRef(v_ref_3822_, v___y_3907_);
                v___x_3910_ = l_Lean_Syntax_getPos_x3f(v_ref_3909_, v___y_3906_);
                if lean_obj_tag(v___x_3910_) == 0 {
                    v___x_3911_ = lean_unsigned_to_nat(0);
                    v___y_3891_ = v___y_3902_;
                    v___y_3892_ = v___y_3908_;
                    v___y_3893_ = v___y_3903_;
                    v___y_3894_ = v___y_3904_;
                    v___y_3895_ = v___y_3905_;
                    v___y_3896_ = v_ref_3909_;
                    v___y_3897_ = v___y_3906_;
                    v___y_3898_ = v___x_3911_;
                    state = 7;
                    continue;
                } else {
                    v_val_3912_ = lean_ctor_get(v___x_3910_, 0);
                    lean_inc(v_val_3912_);
                    lean_dec_ref_known(v___x_3910_, 1);
                    v___y_3891_ = v___y_3902_;
                    v___y_3892_ = v___y_3908_;
                    v___y_3893_ = v___y_3903_;
                    v___y_3894_ = v___y_3904_;
                    v___y_3895_ = v___y_3905_;
                    v___y_3896_ = v_ref_3909_;
                    v___y_3897_ = v___y_3906_;
                    v___y_3898_ = v_val_3912_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_3921_ == 0 {
                    v___y_3902_ = v___y_3915_;
                    v___y_3903_ = v___y_3916_;
                    v___y_3904_ = v___y_3917_;
                    v___y_3905_ = v___y_3918_;
                    v___y_3906_ = v___y_3920_;
                    v___y_3907_ = v___y_3919_;
                    v___y_3908_ = v_severity_3824_;
                    state = 8;
                    continue;
                } else {
                    v___y_3902_ = v___y_3915_;
                    v___y_3903_ = v___y_3916_;
                    v___y_3904_ = v___y_3917_;
                    v___y_3905_ = v___y_3918_;
                    v___y_3906_ = v___y_3920_;
                    v___y_3907_ = v___y_3919_;
                    v___y_3908_ = v___x_3913_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_3923_ == 0 {
                    v_fileName_3924_ = lean_ctor_get(v___y_3826_, 0);
                    v_fileMap_3925_ = lean_ctor_get(v___y_3826_, 1);
                    v_options_3926_ = lean_ctor_get(v___y_3826_, 2);
                    v_ref_3927_ = lean_ctor_get(v___y_3826_, 5);
                    v_suppressElabErrors_3928_ = lean_ctor_get_uint8(
                        v___y_3826_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_3929_ = lean_box((v___y_3923_) as usize);
                    v___x_3930_ = lean_box((v_suppressElabErrors_3928_) as usize);
                    v___f_3931_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_3931_, 0, v___x_3929_);
                    lean_closure_set(v___f_3931_, 1, v___x_3930_);
                    v___x_3932_ = 1;
                    v___x_3933_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3824_, v___x_3932_);
                    if v___x_3933_ == 0 {
                        v___y_3915_ = v___f_3931_;
                        v___y_3916_ = v_suppressElabErrors_3928_;
                        v___y_3917_ = v_fileMap_3925_;
                        v___y_3918_ = v_fileName_3924_;
                        v___y_3919_ = v_ref_3927_;
                        v___y_3920_ = v___y_3923_;
                        v___y_3921_ = v___x_3933_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3934_ = l_Lean_warningAsError;
                        v___x_3935_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_3926_, v___x_3934_);
                        v___y_3915_ = v___f_3931_;
                        v___y_3916_ = v_suppressElabErrors_3928_;
                        v___y_3917_ = v_fileMap_3925_;
                        v___y_3918_ = v_fileName_3924_;
                        v___y_3919_ = v_ref_3927_;
                        v___y_3920_ = v___y_3923_;
                        v___y_3921_ = v___x_3935_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_3823_);
                    v___x_3936_ = lean_box(0);
                    v___x_3937_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3937_, 0, v___x_3936_);
                    return v___x_3937_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___boxed(
    mut v_ref_3940_: *mut LeanObject,
    mut v_msgData_3941_: *mut LeanObject,
    mut v_severity_3942_: *mut LeanObject,
    mut v_isSilent_3943_: *mut LeanObject,
    mut v___y_3944_: *mut LeanObject,
    mut v___y_3945_: *mut LeanObject,
    mut v___y_3946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_3947_: u8 = 0;
    let mut v_isSilent_boxed_3948_: u8 = 0;
    let mut v_res_3949_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_3947_ = (lean_unbox(v_severity_3942_) as u8);
    v_isSilent_boxed_3948_ = (lean_unbox(v_isSilent_3943_) as u8);
    v_res_3949_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(v_ref_3940_, v_msgData_3941_, v_severity_boxed_3947_, v_isSilent_boxed_3948_, v___y_3944_, v___y_3945_);
    lean_dec(v___y_3945_);
    lean_dec_ref(v___y_3944_);
    lean_dec(v_ref_3940_);
    return v_res_3949_;
}
pub unsafe fn l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(
    mut v_ref_3950_: *mut LeanObject,
    mut v_msgData_3951_: *mut LeanObject,
    mut v___y_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3955_: u8 = 0;
    let mut v___x_3956_: u8 = 0;
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    v___x_3955_ = 0;
    v___x_3956_ = 0;
    v___x_3957_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(v_ref_3950_, v_msgData_3951_, v___x_3955_, v___x_3956_, v___y_3952_, v___y_3953_);
    return v___x_3957_;
}
pub unsafe fn l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0___boxed(
    mut v_ref_3958_: *mut LeanObject,
    mut v_msgData_3959_: *mut LeanObject,
    mut v___y_3960_: *mut LeanObject,
    mut v___y_3961_: *mut LeanObject,
    mut v___y_3962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3963_: *mut LeanObject = core::ptr::null_mut();
    v_res_3963_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(
        v_ref_3958_,
        v_msgData_3959_,
        v___y_3960_,
        v___y_3961_,
    );
    lean_dec(v___y_3961_);
    lean_dec_ref(v___y_3960_);
    lean_dec(v_ref_3958_);
    return v_res_3963_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addSuggestion(
    mut v_ref_3964_: *mut LeanObject,
    mut v_s_3965_: *mut LeanObject,
    mut v_origSpan_x3f_3966_: *mut LeanObject,
    mut v_header_3967_: *mut LeanObject,
    mut v_codeActionPrefix_x3f_3968_: *mut LeanObject,
    mut v_diffGranularity_3969_: u8,
    mut v_footer_3970_: *mut LeanObject,
    mut v_a_3971_: *mut LeanObject,
    mut v_a_3972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hintSuggestion_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: u8 = 0;
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3989_: u8 = 0;
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3974_ = lean_box(0);
                v_hintSuggestion_3975_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v_hintSuggestion_3975_, 0, v_s_3965_);
                lean_ctor_set(v_hintSuggestion_3975_, 1, v_origSpan_x3f_3966_);
                lean_ctor_set(v_hintSuggestion_3975_, 2, v___x_3974_);
                lean_ctor_set_uint8(
                    v_hintSuggestion_3975_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_diffGranularity_3969_,
                );
                v___x_3976_ = lean_unsigned_to_nat(1);
                v___x_3977_ = lean_mk_empty_array_with_capacity(v___x_3976_);
                v___x_3978_ = lean_array_push(v___x_3977_, v_hintSuggestion_3975_);
                v___x_3979_ = 0;
                lean_inc(v_ref_3964_);
                v___x_3980_ = l_Lean_Meta_Hint_mkSuggestionsMessage(
                    v___x_3978_,
                    v_ref_3964_,
                    v_codeActionPrefix_x3f_3968_,
                    v___x_3979_,
                    v_a_3971_,
                    v_a_3972_,
                );
                lean_dec_ref(v___x_3978_);
                if lean_obj_tag(v___x_3980_) == 0 {
                    v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
                    lean_inc(v_a_3981_);
                    lean_dec_ref_known(v___x_3980_, 1);
                    v___x_3982_ = l_Lean_stringToMessageData(v_header_3967_);
                    v___x_3983_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3983_, 0, v___x_3982_);
                    lean_ctor_set(v___x_3983_, 1, v_a_3981_);
                    v___x_3984_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3984_, 0, v___x_3983_);
                    lean_ctor_set(v___x_3984_, 1, v_footer_3970_);
                    v___x_3985_ =
                        l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(
                            v_ref_3964_,
                            v___x_3984_,
                            v_a_3971_,
                            v_a_3972_,
                        );
                    lean_dec(v_ref_3964_);
                    return v___x_3985_;
                } else {
                    lean_dec_ref(v_footer_3970_);
                    lean_dec_ref(v_header_3967_);
                    lean_dec(v_ref_3964_);
                    v_a_3986_ = lean_ctor_get(v___x_3980_, 0);
                    v_isSharedCheck_3993_ = (!lean_is_exclusive(v___x_3980_)) as u8;
                    if v_isSharedCheck_3993_ == 0 {
                        v___x_3988_ = v___x_3980_;
                        v_isShared_3989_ = v_isSharedCheck_3993_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3986_);
                        lean_dec(v___x_3980_);
                        v___x_3988_ = lean_box(0);
                        v_isShared_3989_ = v_isSharedCheck_3993_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3989_ == 0 {
                    v___x_3991_ = v___x_3988_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
                    v___x_3991_ = v_reuseFailAlloc_3992_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addSuggestion___boxed(
    mut v_ref_3994_: *mut LeanObject,
    mut v_s_3995_: *mut LeanObject,
    mut v_origSpan_x3f_3996_: *mut LeanObject,
    mut v_header_3997_: *mut LeanObject,
    mut v_codeActionPrefix_x3f_3998_: *mut LeanObject,
    mut v_diffGranularity_3999_: *mut LeanObject,
    mut v_footer_4000_: *mut LeanObject,
    mut v_a_4001_: *mut LeanObject,
    mut v_a_4002_: *mut LeanObject,
    mut v_a_4003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_diffGranularity_boxed_4004_: u8 = 0;
    let mut v_res_4005_: *mut LeanObject = core::ptr::null_mut();
    v_diffGranularity_boxed_4004_ = (lean_unbox(v_diffGranularity_3999_) as u8);
    v_res_4005_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
        v_ref_3994_,
        v_s_3995_,
        v_origSpan_x3f_3996_,
        v_header_3997_,
        v_codeActionPrefix_x3f_3998_,
        v_diffGranularity_boxed_4004_,
        v_footer_4000_,
        v_a_4001_,
        v_a_4002_,
    );
    lean_dec(v_a_4002_);
    lean_dec_ref(v_a_4001_);
    return v_res_4005_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(
    mut v_msg_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4015_: u8 = 0;
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4010_ = lean_ctor_get(v___y_4007_, 5);
                v___x_4011_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v_msg_4006_, v___y_4007_, v___y_4008_);
                v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
                v_isSharedCheck_4020_ = (!lean_is_exclusive(v___x_4011_)) as u8;
                if v_isSharedCheck_4020_ == 0 {
                    v___x_4014_ = v___x_4011_;
                    v_isShared_4015_ = v_isSharedCheck_4020_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4012_);
                    lean_dec(v___x_4011_);
                    v___x_4014_ = lean_box(0);
                    v_isShared_4015_ = v_isSharedCheck_4020_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4010_);
                v___x_4016_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4016_, 0, v_ref_4010_);
                lean_ctor_set(v___x_4016_, 1, v_a_4012_);
                if v_isShared_4015_ == 0 {
                    lean_ctor_set_tag(v___x_4014_, 1);
                    lean_ctor_set(v___x_4014_, 0, v___x_4016_);
                    v___x_4018_ = v___x_4014_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4016_);
                    v___x_4018_ = v_reuseFailAlloc_4019_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg___boxed(
    mut v_msg_4021_: *mut LeanObject,
    mut v___y_4022_: *mut LeanObject,
    mut v___y_4023_: *mut LeanObject,
    mut v___y_4024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4025_: *mut LeanObject = core::ptr::null_mut();
    v_res_4025_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_4021_, v___y_4022_, v___y_4023_);
    lean_dec(v___y_4023_);
    lean_dec_ref(v___y_4022_);
    return v_res_4025_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(
    mut v_ref_4026_: *mut LeanObject,
    mut v_msg_4027_: *mut LeanObject,
    mut v___y_4028_: *mut LeanObject,
    mut v___y_4029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4043_: u8 = 0;
    let mut v_cancelTk_x3f_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4045_: u8 = 0;
    let mut v_inheritedTraceOptions_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_4031_ = lean_ctor_get(v___y_4028_, 0);
    v_fileMap_4032_ = lean_ctor_get(v___y_4028_, 1);
    v_options_4033_ = lean_ctor_get(v___y_4028_, 2);
    v_currRecDepth_4034_ = lean_ctor_get(v___y_4028_, 3);
    v_maxRecDepth_4035_ = lean_ctor_get(v___y_4028_, 4);
    v_ref_4036_ = lean_ctor_get(v___y_4028_, 5);
    v_currNamespace_4037_ = lean_ctor_get(v___y_4028_, 6);
    v_openDecls_4038_ = lean_ctor_get(v___y_4028_, 7);
    v_initHeartbeats_4039_ = lean_ctor_get(v___y_4028_, 8);
    v_maxHeartbeats_4040_ = lean_ctor_get(v___y_4028_, 9);
    v_quotContext_4041_ = lean_ctor_get(v___y_4028_, 10);
    v_currMacroScope_4042_ = lean_ctor_get(v___y_4028_, 11);
    v_diag_4043_ = lean_ctor_get_uint8(
        v___y_4028_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4044_ = lean_ctor_get(v___y_4028_, 12);
    v_suppressElabErrors_4045_ = lean_ctor_get_uint8(
        v___y_4028_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4046_ = lean_ctor_get(v___y_4028_, 13);
    v_ref_4047_ = l_Lean_replaceRef(v_ref_4026_, v_ref_4036_);
    lean_inc_ref(v_inheritedTraceOptions_4046_);
    lean_inc(v_cancelTk_x3f_4044_);
    lean_inc(v_currMacroScope_4042_);
    lean_inc(v_quotContext_4041_);
    lean_inc(v_maxHeartbeats_4040_);
    lean_inc(v_initHeartbeats_4039_);
    lean_inc(v_openDecls_4038_);
    lean_inc(v_currNamespace_4037_);
    lean_inc(v_maxRecDepth_4035_);
    lean_inc(v_currRecDepth_4034_);
    lean_inc_ref(v_options_4033_);
    lean_inc_ref(v_fileMap_4032_);
    lean_inc_ref(v_fileName_4031_);
    v___x_4048_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_4048_, 0, v_fileName_4031_);
    lean_ctor_set(v___x_4048_, 1, v_fileMap_4032_);
    lean_ctor_set(v___x_4048_, 2, v_options_4033_);
    lean_ctor_set(v___x_4048_, 3, v_currRecDepth_4034_);
    lean_ctor_set(v___x_4048_, 4, v_maxRecDepth_4035_);
    lean_ctor_set(v___x_4048_, 5, v_ref_4047_);
    lean_ctor_set(v___x_4048_, 6, v_currNamespace_4037_);
    lean_ctor_set(v___x_4048_, 7, v_openDecls_4038_);
    lean_ctor_set(v___x_4048_, 8, v_initHeartbeats_4039_);
    lean_ctor_set(v___x_4048_, 9, v_maxHeartbeats_4040_);
    lean_ctor_set(v___x_4048_, 10, v_quotContext_4041_);
    lean_ctor_set(v___x_4048_, 11, v_currMacroScope_4042_);
    lean_ctor_set(v___x_4048_, 12, v_cancelTk_x3f_4044_);
    lean_ctor_set(v___x_4048_, 13, v_inheritedTraceOptions_4046_);
    lean_ctor_set_uint8(
        v___x_4048_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_4043_,
    );
    lean_ctor_set_uint8(
        v___x_4048_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4045_,
    );
    v___x_4049_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_4027_, v___x_4048_, v___y_4029_);
    lean_dec_ref_known(v___x_4048_, 14);
    return v___x_4049_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg___boxed(
    mut v_ref_4050_: *mut LeanObject,
    mut v_msg_4051_: *mut LeanObject,
    mut v___y_4052_: *mut LeanObject,
    mut v___y_4053_: *mut LeanObject,
    mut v___y_4054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4055_: *mut LeanObject = core::ptr::null_mut();
    v_res_4055_ =
        l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(
            v_ref_4050_,
            v_msg_4051_,
            v___y_4052_,
            v___y_4053_,
        );
    lean_dec(v___y_4053_);
    lean_dec_ref(v___y_4052_);
    lean_dec(v_ref_4050_);
    return v_res_4055_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(
    mut v_origSpan_x3f_4056_: *mut LeanObject,
    mut v_diffGranularity_4057_: u8,
    mut v_sz_4058_: usize,
    mut v_i_4059_: usize,
    mut v_bs_4060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4061_: u8 = 0;
    let mut v_v_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: usize = 0;
    let mut v___x_4068_: usize = 0;
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4061_ = lean_usize_dec_lt(v_i_4059_, v_sz_4058_);
                if v___x_4061_ == 0 {
                    lean_dec(v_origSpan_x3f_4056_);
                    return v_bs_4060_;
                } else {
                    v_v_4062_ = lean_array_uget(v_bs_4060_, v_i_4059_);
                    v___x_4063_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4064_ = lean_array_uset(v_bs_4060_, v_i_4059_, v___x_4063_);
                    v___x_4065_ = lean_box(0);
                    lean_inc(v_origSpan_x3f_4056_);
                    v___x_4066_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v___x_4066_, 0, v_v_4062_);
                    lean_ctor_set(v___x_4066_, 1, v_origSpan_x3f_4056_);
                    lean_ctor_set(v___x_4066_, 2, v___x_4065_);
                    lean_ctor_set_uint8(
                        v___x_4066_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_diffGranularity_4057_,
                    );
                    v___x_4067_ = 1usize;
                    v___x_4068_ = lean_usize_add(v_i_4059_, v___x_4067_);
                    v___x_4069_ = lean_array_uset(v_bs_x27_4064_, v_i_4059_, v___x_4066_);
                    v_i_4059_ = v___x_4068_;
                    v_bs_4060_ = v___x_4069_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0___boxed(
    mut v_origSpan_x3f_4071_: *mut LeanObject,
    mut v_diffGranularity_4072_: *mut LeanObject,
    mut v_sz_4073_: *mut LeanObject,
    mut v_i_4074_: *mut LeanObject,
    mut v_bs_4075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_diffGranularity_boxed_4076_: u8 = 0;
    let mut v_sz_boxed_4077_: usize = 0;
    let mut v_i_boxed_4078_: usize = 0;
    let mut v_res_4079_: *mut LeanObject = core::ptr::null_mut();
    v_diffGranularity_boxed_4076_ = (lean_unbox(v_diffGranularity_4072_) as u8);
    v_sz_boxed_4077_ = lean_unbox_usize(v_sz_4073_);
    lean_dec(v_sz_4073_);
    v_i_boxed_4078_ = lean_unbox_usize(v_i_4074_);
    lean_dec(v_i_4074_);
    v_res_4079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(v_origSpan_x3f_4071_, v_diffGranularity_boxed_4076_, v_sz_boxed_4077_, v_i_boxed_4078_, v_bs_4075_);
    return v_res_4079_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    v___x_4081_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__0;
    v___x_4082_ = l_Lean_stringToMessageData(v___x_4081_);
    return v___x_4082_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(
    mut v_ref_4083_: *mut LeanObject,
    mut v_suggestions_4084_: *mut LeanObject,
    mut v_origSpan_x3f_4085_: *mut LeanObject,
    mut v_header_4086_: *mut LeanObject,
    mut v_codeActionPrefix_x3f_4087_: *mut LeanObject,
    mut v_diffGranularity_4088_: u8,
    mut v_footer_4089_: *mut LeanObject,
    mut v_a_4090_: *mut LeanObject,
    mut v_a_4091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4096_: usize = 0;
    let mut v___x_4097_: usize = 0;
    let mut v_hintSuggestions_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4109_: u8 = 0;
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4113_: u8 = 0;
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: u8 = 0;
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4114_ = lean_array_get_size(v_suggestions_4084_);
                v___x_4115_ = lean_unsigned_to_nat(0);
                v___x_4116_ = lean_nat_dec_eq(v___x_4114_, v___x_4115_);
                if v___x_4116_ == 0 {
                    v___y_4094_ = v_a_4090_;
                    v___y_4095_ = v_a_4091_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_footer_4089_);
                    lean_dec(v_codeActionPrefix_x3f_4087_);
                    lean_dec_ref(v_header_4086_);
                    lean_dec(v_origSpan_x3f_4085_);
                    lean_dec_ref(v_suggestions_4084_);
                    v___x_4117_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1_once
                        ),
                        _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1,
                    );
                    v___x_4118_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_4083_, v___x_4117_, v_a_4090_, v_a_4091_);
                    lean_dec(v_ref_4083_);
                    return v___x_4118_;
                }
            }
            1 => {
                v_sz_4096_ = lean_array_size(v_suggestions_4084_);
                v___x_4097_ = 0usize;
                v_hintSuggestions_4098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(v_origSpan_x3f_4085_, v_diffGranularity_4088_, v_sz_4096_, v___x_4097_, v_suggestions_4084_);
                v___x_4099_ = 1;
                lean_inc(v_ref_4083_);
                v___x_4100_ = l_Lean_Meta_Hint_mkSuggestionsMessage(
                    v_hintSuggestions_4098_,
                    v_ref_4083_,
                    v_codeActionPrefix_x3f_4087_,
                    v___x_4099_,
                    v___y_4094_,
                    v___y_4095_,
                );
                lean_dec_ref(v_hintSuggestions_4098_);
                if lean_obj_tag(v___x_4100_) == 0 {
                    v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
                    lean_inc(v_a_4101_);
                    lean_dec_ref_known(v___x_4100_, 1);
                    v___x_4102_ = l_Lean_stringToMessageData(v_header_4086_);
                    v___x_4103_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4103_, 0, v___x_4102_);
                    lean_ctor_set(v___x_4103_, 1, v_a_4101_);
                    v___x_4104_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4104_, 0, v___x_4103_);
                    lean_ctor_set(v___x_4104_, 1, v_footer_4089_);
                    v___x_4105_ =
                        l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(
                            v_ref_4083_,
                            v___x_4104_,
                            v___y_4094_,
                            v___y_4095_,
                        );
                    lean_dec(v_ref_4083_);
                    return v___x_4105_;
                } else {
                    lean_dec_ref(v_footer_4089_);
                    lean_dec_ref(v_header_4086_);
                    lean_dec(v_ref_4083_);
                    v_a_4106_ = lean_ctor_get(v___x_4100_, 0);
                    v_isSharedCheck_4113_ = (!lean_is_exclusive(v___x_4100_)) as u8;
                    if v_isSharedCheck_4113_ == 0 {
                        v___x_4108_ = v___x_4100_;
                        v_isShared_4109_ = v_isSharedCheck_4113_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4106_);
                        lean_dec(v___x_4100_);
                        v___x_4108_ = lean_box(0);
                        v_isShared_4109_ = v_isSharedCheck_4113_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4109_ == 0 {
                    v___x_4111_ = v___x_4108_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4106_);
                    v___x_4111_ = v_reuseFailAlloc_4112_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___boxed(
    mut v_ref_4119_: *mut LeanObject,
    mut v_suggestions_4120_: *mut LeanObject,
    mut v_origSpan_x3f_4121_: *mut LeanObject,
    mut v_header_4122_: *mut LeanObject,
    mut v_codeActionPrefix_x3f_4123_: *mut LeanObject,
    mut v_diffGranularity_4124_: *mut LeanObject,
    mut v_footer_4125_: *mut LeanObject,
    mut v_a_4126_: *mut LeanObject,
    mut v_a_4127_: *mut LeanObject,
    mut v_a_4128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_diffGranularity_boxed_4129_: u8 = 0;
    let mut v_res_4130_: *mut LeanObject = core::ptr::null_mut();
    v_diffGranularity_boxed_4129_ = (lean_unbox(v_diffGranularity_4124_) as u8);
    v_res_4130_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(
        v_ref_4119_,
        v_suggestions_4120_,
        v_origSpan_x3f_4121_,
        v_header_4122_,
        v_codeActionPrefix_x3f_4123_,
        v_diffGranularity_boxed_4129_,
        v_footer_4125_,
        v_a_4126_,
        v_a_4127_,
    );
    lean_dec(v_a_4127_);
    lean_dec_ref(v_a_4126_);
    return v_res_4130_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addSuggestions(
    mut v_ref_4131_: *mut LeanObject,
    mut v_suggestions_4132_: *mut LeanObject,
    mut v_origSpan_x3f_4133_: *mut LeanObject,
    mut v_header_4134_: *mut LeanObject,
    mut v_style_x3f_4135_: *mut LeanObject,
    mut v_codeActionPrefix_x3f_4136_: *mut LeanObject,
    mut v_diffGranularity_4137_: u8,
    mut v_footer_4138_: *mut LeanObject,
    mut v_a_4139_: *mut LeanObject,
    mut v_a_4140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    v___x_4142_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(
        v_ref_4131_,
        v_suggestions_4132_,
        v_origSpan_x3f_4133_,
        v_header_4134_,
        v_codeActionPrefix_x3f_4136_,
        v_diffGranularity_4137_,
        v_footer_4138_,
        v_a_4139_,
        v_a_4140_,
    );
    return v___x_4142_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addSuggestions___boxed(
    mut v_ref_4143_: *mut LeanObject,
    mut v_suggestions_4144_: *mut LeanObject,
    mut v_origSpan_x3f_4145_: *mut LeanObject,
    mut v_header_4146_: *mut LeanObject,
    mut v_style_x3f_4147_: *mut LeanObject,
    mut v_codeActionPrefix_x3f_4148_: *mut LeanObject,
    mut v_diffGranularity_4149_: *mut LeanObject,
    mut v_footer_4150_: *mut LeanObject,
    mut v_a_4151_: *mut LeanObject,
    mut v_a_4152_: *mut LeanObject,
    mut v_a_4153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_diffGranularity_boxed_4154_: u8 = 0;
    let mut v_res_4155_: *mut LeanObject = core::ptr::null_mut();
    v_diffGranularity_boxed_4154_ = (lean_unbox(v_diffGranularity_4149_) as u8);
    v_res_4155_ = l_Lean_Meta_Tactic_TryThis_addSuggestions(
        v_ref_4143_,
        v_suggestions_4144_,
        v_origSpan_x3f_4145_,
        v_header_4146_,
        v_style_x3f_4147_,
        v_codeActionPrefix_x3f_4148_,
        v_diffGranularity_boxed_4154_,
        v_footer_4150_,
        v_a_4151_,
        v_a_4152_,
    );
    lean_dec(v_a_4152_);
    lean_dec_ref(v_a_4151_);
    lean_dec(v_style_x3f_4147_);
    return v_res_4155_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(
    mut v_00_u03b1_4156_: *mut LeanObject,
    mut v_ref_4157_: *mut LeanObject,
    mut v_msg_4158_: *mut LeanObject,
    mut v___y_4159_: *mut LeanObject,
    mut v___y_4160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    v___x_4162_ =
        l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(
            v_ref_4157_,
            v_msg_4158_,
            v___y_4159_,
            v___y_4160_,
        );
    return v___x_4162_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___boxed(
    mut v_00_u03b1_4163_: *mut LeanObject,
    mut v_ref_4164_: *mut LeanObject,
    mut v_msg_4165_: *mut LeanObject,
    mut v___y_4166_: *mut LeanObject,
    mut v___y_4167_: *mut LeanObject,
    mut v___y_4168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4169_: *mut LeanObject = core::ptr::null_mut();
    v_res_4169_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(
        v_00_u03b1_4163_,
        v_ref_4164_,
        v_msg_4165_,
        v___y_4166_,
        v___y_4167_,
    );
    lean_dec(v___y_4167_);
    lean_dec_ref(v___y_4166_);
    lean_dec(v_ref_4164_);
    return v_res_4169_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1(
    mut v_00_u03b1_4170_: *mut LeanObject,
    mut v_msg_4171_: *mut LeanObject,
    mut v___y_4172_: *mut LeanObject,
    mut v___y_4173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    v___x_4175_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_4171_, v___y_4172_, v___y_4173_);
    return v___x_4175_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___boxed(
    mut v_00_u03b1_4176_: *mut LeanObject,
    mut v_msg_4177_: *mut LeanObject,
    mut v___y_4178_: *mut LeanObject,
    mut v___y_4179_: *mut LeanObject,
    mut v___y_4180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4181_: *mut LeanObject = core::ptr::null_mut();
    v_res_4181_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1(v_00_u03b1_4176_, v_msg_4177_, v___y_4178_, v___y_4179_);
    lean_dec(v___y_4179_);
    lean_dec_ref(v___y_4178_);
    return v_res_4181_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(
    mut v_a_4182_: *mut LeanObject,
    mut v___y_4183_: *mut LeanObject,
    mut v___y_4184_: *mut LeanObject,
    mut v___y_4185_: *mut LeanObject,
    mut v___y_4186_: *mut LeanObject,
    mut v___y_4187_: *mut LeanObject,
    mut v___y_4188_: *mut LeanObject,
    mut v___y_4189_: *mut LeanObject,
    mut v___y_4190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4184_);
    lean_inc_ref(v___y_4183_);
    v___x_4192_ = lean_apply_2(v_a_4182_, v___y_4183_, v___y_4184_);
    v___x_4193_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v___x_4192_,
        v___y_4185_,
        v___y_4186_,
        v___y_4187_,
        v___y_4188_,
        v___y_4189_,
        v___y_4190_,
    );
    return v___x_4193_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg___boxed(
    mut v_a_4194_: *mut LeanObject,
    mut v___y_4195_: *mut LeanObject,
    mut v___y_4196_: *mut LeanObject,
    mut v___y_4197_: *mut LeanObject,
    mut v___y_4198_: *mut LeanObject,
    mut v___y_4199_: *mut LeanObject,
    mut v___y_4200_: *mut LeanObject,
    mut v___y_4201_: *mut LeanObject,
    mut v___y_4202_: *mut LeanObject,
    mut v___y_4203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4204_: *mut LeanObject = core::ptr::null_mut();
    v_res_4204_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v_a_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
    lean_dec(v___y_4202_);
    lean_dec_ref(v___y_4201_);
    lean_dec(v___y_4200_);
    lean_dec_ref(v___y_4199_);
    lean_dec(v___y_4198_);
    lean_dec_ref(v___y_4197_);
    lean_dec(v___y_4196_);
    lean_dec_ref(v___y_4195_);
    return v_res_4204_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0(
    mut v_00_u03b1_4205_: *mut LeanObject,
    mut v_a_4206_: *mut LeanObject,
    mut v___y_4207_: *mut LeanObject,
    mut v___y_4208_: *mut LeanObject,
    mut v___y_4209_: *mut LeanObject,
    mut v___y_4210_: *mut LeanObject,
    mut v___y_4211_: *mut LeanObject,
    mut v___y_4212_: *mut LeanObject,
    mut v___y_4213_: *mut LeanObject,
    mut v___y_4214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    v___x_4216_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v_a_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
    return v___x_4216_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___boxed(
    mut v_00_u03b1_4217_: *mut LeanObject,
    mut v_a_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
    mut v___y_4220_: *mut LeanObject,
    mut v___y_4221_: *mut LeanObject,
    mut v___y_4222_: *mut LeanObject,
    mut v___y_4223_: *mut LeanObject,
    mut v___y_4224_: *mut LeanObject,
    mut v___y_4225_: *mut LeanObject,
    mut v___y_4226_: *mut LeanObject,
    mut v___y_4227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4228_: *mut LeanObject = core::ptr::null_mut();
    v_res_4228_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0(v_00_u03b1_4217_, v_a_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
    lean_dec(v___y_4226_);
    lean_dec_ref(v___y_4225_);
    lean_dec(v___y_4224_);
    lean_dec_ref(v___y_4223_);
    lean_dec(v___y_4222_);
    lean_dec_ref(v___y_4221_);
    lean_dec(v___y_4220_);
    lean_dec_ref(v___y_4219_);
    return v_res_4228_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(
    mut v_e_4229_: *mut LeanObject,
    mut v___y_4230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4232_: u8 = 0;
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4246_: u8 = 0;
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4252_: u8 = 0;
    let mut v_unused_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4232_ = l_Lean_Expr_hasMVar(v_e_4229_);
                if v___x_4232_ == 0 {
                    v___x_4233_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4233_, 0, v_e_4229_);
                    return v___x_4233_;
                } else {
                    v___x_4234_ = lean_st_ref_get(v___y_4230_);
                    v_mctx_4235_ = lean_ctor_get(v___x_4234_, 0);
                    lean_inc_ref(v_mctx_4235_);
                    lean_dec(v___x_4234_);
                    v___x_4236_ = l_Lean_instantiateMVarsCore(v_mctx_4235_, v_e_4229_);
                    v_fst_4237_ = lean_ctor_get(v___x_4236_, 0);
                    lean_inc(v_fst_4237_);
                    v_snd_4238_ = lean_ctor_get(v___x_4236_, 1);
                    lean_inc(v_snd_4238_);
                    lean_dec_ref(v___x_4236_);
                    v___x_4239_ = lean_st_ref_take(v___y_4230_);
                    v_cache_4240_ = lean_ctor_get(v___x_4239_, 1);
                    v_zetaDeltaFVarIds_4241_ = lean_ctor_get(v___x_4239_, 2);
                    v_postponed_4242_ = lean_ctor_get(v___x_4239_, 3);
                    v_diag_4243_ = lean_ctor_get(v___x_4239_, 4);
                    v_isSharedCheck_4252_ = (!lean_is_exclusive(v___x_4239_)) as u8;
                    if v_isSharedCheck_4252_ == 0 {
                        v_unused_4253_ = lean_ctor_get(v___x_4239_, 0);
                        lean_dec(v_unused_4253_);
                        v___x_4245_ = v___x_4239_;
                        v_isShared_4246_ = v_isSharedCheck_4252_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_4243_);
                        lean_inc(v_postponed_4242_);
                        lean_inc(v_zetaDeltaFVarIds_4241_);
                        lean_inc(v_cache_4240_);
                        lean_dec(v___x_4239_);
                        v___x_4245_ = lean_box(0);
                        v_isShared_4246_ = v_isSharedCheck_4252_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4246_ == 0 {
                    lean_ctor_set(v___x_4245_, 0, v_snd_4238_);
                    v___x_4248_ = v___x_4245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_snd_4238_);
                    lean_ctor_set(v_reuseFailAlloc_4251_, 1, v_cache_4240_);
                    lean_ctor_set(v_reuseFailAlloc_4251_, 2, v_zetaDeltaFVarIds_4241_);
                    lean_ctor_set(v_reuseFailAlloc_4251_, 3, v_postponed_4242_);
                    lean_ctor_set(v_reuseFailAlloc_4251_, 4, v_diag_4243_);
                    v___x_4248_ = v_reuseFailAlloc_4251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4249_ = lean_st_ref_set(v___y_4230_, v___x_4248_);
                v___x_4250_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4250_, 0, v_fst_4237_);
                return v___x_4250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg___boxed(
    mut v_e_4254_: *mut LeanObject,
    mut v___y_4255_: *mut LeanObject,
    mut v___y_4256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4257_: *mut LeanObject = core::ptr::null_mut();
    v_res_4257_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_4254_, v___y_4255_);
    lean_dec(v___y_4255_);
    return v_res_4257_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(
    mut v_e_4258_: *mut LeanObject,
    mut v___y_4259_: *mut LeanObject,
    mut v___y_4260_: *mut LeanObject,
    mut v___y_4261_: *mut LeanObject,
    mut v___y_4262_: *mut LeanObject,
    mut v___y_4263_: *mut LeanObject,
    mut v___y_4264_: *mut LeanObject,
    mut v___y_4265_: *mut LeanObject,
    mut v___y_4266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    v___x_4268_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_4258_, v___y_4264_);
    return v___x_4268_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___boxed(
    mut v_e_4269_: *mut LeanObject,
    mut v___y_4270_: *mut LeanObject,
    mut v___y_4271_: *mut LeanObject,
    mut v___y_4272_: *mut LeanObject,
    mut v___y_4273_: *mut LeanObject,
    mut v___y_4274_: *mut LeanObject,
    mut v___y_4275_: *mut LeanObject,
    mut v___y_4276_: *mut LeanObject,
    mut v___y_4277_: *mut LeanObject,
    mut v___y_4278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4279_: *mut LeanObject = core::ptr::null_mut();
    v_res_4279_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(v_e_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
    lean_dec(v___y_4277_);
    lean_dec_ref(v___y_4276_);
    lean_dec(v___y_4275_);
    lean_dec_ref(v___y_4274_);
    lean_dec(v___y_4273_);
    lean_dec_ref(v___y_4272_);
    lean_dec(v___y_4271_);
    lean_dec_ref(v___y_4270_);
    return v_res_4279_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(
    mut v_msg_4280_: *mut LeanObject,
    mut v___y_4281_: *mut LeanObject,
    mut v___y_4282_: *mut LeanObject,
    mut v___y_4283_: *mut LeanObject,
    mut v___y_4284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4291_: u8 = 0;
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4286_ = lean_ctor_get(v___y_4283_, 5);
                v___x_4287_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_msg_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
                v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
                v_isSharedCheck_4296_ = (!lean_is_exclusive(v___x_4287_)) as u8;
                if v_isSharedCheck_4296_ == 0 {
                    v___x_4290_ = v___x_4287_;
                    v_isShared_4291_ = v_isSharedCheck_4296_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4288_);
                    lean_dec(v___x_4287_);
                    v___x_4290_ = lean_box(0);
                    v_isShared_4291_ = v_isSharedCheck_4296_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4286_);
                v___x_4292_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4292_, 0, v_ref_4286_);
                lean_ctor_set(v___x_4292_, 1, v_a_4288_);
                if v_isShared_4291_ == 0 {
                    lean_ctor_set_tag(v___x_4290_, 1);
                    lean_ctor_set(v___x_4290_, 0, v___x_4292_);
                    v___x_4294_ = v___x_4290_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4292_);
                    v___x_4294_ = v_reuseFailAlloc_4295_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg___boxed(
    mut v_msg_4297_: *mut LeanObject,
    mut v___y_4298_: *mut LeanObject,
    mut v___y_4299_: *mut LeanObject,
    mut v___y_4300_: *mut LeanObject,
    mut v___y_4301_: *mut LeanObject,
    mut v___y_4302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4303_: *mut LeanObject = core::ptr::null_mut();
    v_res_4303_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_msg_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
    lean_dec(v___y_4301_);
    lean_dec_ref(v___y_4300_);
    lean_dec(v___y_4299_);
    lean_dec_ref(v___y_4298_);
    return v_res_4303_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1()
-> *mut LeanObject {
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    v___x_4305_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__0;
    v___x_4306_ = l_Lean_stringToMessageData(v___x_4305_);
    return v___x_4306_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(
    mut v_initialState_4307_: *mut LeanObject,
    mut v_tac_4308_: *mut LeanObject,
    mut v_expectedType_x3f_4309_: *mut LeanObject,
    mut v_a_4310_: *mut LeanObject,
    mut v_a_4311_: *mut LeanObject,
    mut v_a_4312_: *mut LeanObject,
    mut v_a_4313_: *mut LeanObject,
    mut v_a_4314_: *mut LeanObject,
    mut v_a_4315_: *mut LeanObject,
    mut v_a_4316_: *mut LeanObject,
    mut v_a_4317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: u8 = 0;
    let mut v_a_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4327_: u8 = 0;
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4331_: u8 = 0;
    let mut v_unused_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4338_: u8 = 0;
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4342_: u8 = 0;
    let mut v_unused_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: u8 = 0;
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4371_: u8 = 0;
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4319_ = l_Lean_Elab_Tactic_saveState___redArg(
                    v_a_4311_, v_a_4313_, v_a_4315_, v_a_4317_,
                );
                if lean_obj_tag(v___x_4319_) == 0 {
                    v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
                    lean_inc(v_a_4320_);
                    lean_dec_ref_known(v___x_4319_, 1);
                    v___x_4321_ = 0;
                    v___x_4348_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v_initialState_4307_,
                        v___x_4321_,
                        v_a_4311_,
                        v_a_4312_,
                        v_a_4313_,
                        v_a_4314_,
                        v_a_4315_,
                        v_a_4316_,
                        v_a_4317_,
                    );
                    if lean_obj_tag(v___x_4348_) == 0 {
                        lean_dec_ref_known(v___x_4348_, 1);
                        v___x_4349_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_evalTactic___boxed as *mut core::ffi::c_void,
                            10,
                            1,
                        );
                        lean_closure_set(v___x_4349_, 0, v_tac_4308_);
                        v___x_4350_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_withoutRecover___boxed as *mut core::ffi::c_void,
                            11,
                            2,
                        );
                        lean_closure_set(v___x_4350_, 0, lean_box(0));
                        lean_closure_set(v___x_4350_, 1, v___x_4349_);
                        v___x_4351_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v___x_4350_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
                        if lean_obj_tag(v___x_4351_) == 0 {
                            lean_dec_ref_known(v___x_4351_, 1);
                            if lean_obj_tag(v_expectedType_x3f_4309_) == 1 {
                                v_val_4352_ = lean_ctor_get(v_expectedType_x3f_4309_, 0);
                                lean_inc(v_val_4352_);
                                lean_dec_ref_known(v_expectedType_x3f_4309_, 1);
                                v___x_4353_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                                    v_a_4311_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_,
                                );
                                if lean_obj_tag(v___x_4353_) == 0 {
                                    v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
                                    lean_inc(v_a_4354_);
                                    lean_dec_ref_known(v___x_4353_, 1);
                                    v___x_4355_ = l_Lean_MVarId_getType(
                                        v_a_4354_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_,
                                    );
                                    if lean_obj_tag(v___x_4355_) == 0 {
                                        v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
                                        lean_inc(v_a_4356_);
                                        lean_dec_ref_known(v___x_4355_, 1);
                                        v___x_4357_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_a_4356_, v_a_4315_);
                                        v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
                                        lean_inc(v_a_4358_);
                                        lean_dec_ref(v___x_4357_);
                                        v___x_4359_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_val_4352_, v_a_4315_);
                                        v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
                                        lean_inc(v_a_4360_);
                                        lean_dec_ref(v___x_4359_);
                                        v___x_4361_ = lean_expr_eqv(v_a_4358_, v_a_4360_);
                                        lean_dec(v_a_4360_);
                                        lean_dec(v_a_4358_);
                                        if v___x_4361_ == 0 {
                                            v___x_4362_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1);
                                            v___x_4363_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v___x_4362_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
                                            v___y_4345_ = v___x_4363_;
                                            state = 7;
                                            continue;
                                        } else {
                                            v___x_4364_ = lean_box(0);
                                            v_a_4334_ = v___x_4364_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_val_4352_);
                                        v_a_4365_ = lean_ctor_get(v___x_4355_, 0);
                                        lean_inc(v_a_4365_);
                                        lean_dec_ref_known(v___x_4355_, 1);
                                        v_a_4323_ = v_a_4365_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_val_4352_);
                                    v_a_4366_ = lean_ctor_get(v___x_4353_, 0);
                                    lean_inc(v_a_4366_);
                                    lean_dec_ref_known(v___x_4353_, 1);
                                    v_a_4323_ = v_a_4366_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_expectedType_x3f_4309_);
                                v___x_4367_ = lean_box(0);
                                v_a_4334_ = v___x_4367_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_expectedType_x3f_4309_);
                            v___y_4345_ = v___x_4351_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4320_);
                        lean_dec(v_expectedType_x3f_4309_);
                        lean_dec(v_tac_4308_);
                        return v___x_4348_;
                    }
                } else {
                    lean_dec(v_expectedType_x3f_4309_);
                    lean_dec(v_tac_4308_);
                    lean_dec_ref(v_initialState_4307_);
                    v_a_4368_ = lean_ctor_get(v___x_4319_, 0);
                    v_isSharedCheck_4375_ = (!lean_is_exclusive(v___x_4319_)) as u8;
                    if v_isSharedCheck_4375_ == 0 {
                        v___x_4370_ = v___x_4319_;
                        v_isShared_4371_ = v_isSharedCheck_4375_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4368_);
                        lean_dec(v___x_4319_);
                        v___x_4370_ = lean_box(0);
                        v_isShared_4371_ = v_isSharedCheck_4375_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4324_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                    v_a_4320_,
                    v___x_4321_,
                    v_a_4311_,
                    v_a_4312_,
                    v_a_4313_,
                    v_a_4314_,
                    v_a_4315_,
                    v_a_4316_,
                    v_a_4317_,
                );
                if lean_obj_tag(v___x_4324_) == 0 {
                    v_isSharedCheck_4331_ = (!lean_is_exclusive(v___x_4324_)) as u8;
                    if v_isSharedCheck_4331_ == 0 {
                        v_unused_4332_ = lean_ctor_get(v___x_4324_, 0);
                        lean_dec(v_unused_4332_);
                        v___x_4326_ = v___x_4324_;
                        v_isShared_4327_ = v_isSharedCheck_4331_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_4324_);
                        v___x_4326_ = lean_box(0);
                        v_isShared_4327_ = v_isSharedCheck_4331_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_4323_);
                    return v___x_4324_;
                }
            }
            2 => {
                if v_isShared_4327_ == 0 {
                    lean_ctor_set_tag(v___x_4326_, 1);
                    lean_ctor_set(v___x_4326_, 0, v_a_4323_);
                    v___x_4329_ = v___x_4326_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4323_);
                    v___x_4329_ = v_reuseFailAlloc_4330_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4329_;
            }
            4 => {
                v___x_4335_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                    v_a_4320_,
                    v___x_4321_,
                    v_a_4311_,
                    v_a_4312_,
                    v_a_4313_,
                    v_a_4314_,
                    v_a_4315_,
                    v_a_4316_,
                    v_a_4317_,
                );
                if lean_obj_tag(v___x_4335_) == 0 {
                    v_isSharedCheck_4342_ = (!lean_is_exclusive(v___x_4335_)) as u8;
                    if v_isSharedCheck_4342_ == 0 {
                        v_unused_4343_ = lean_ctor_get(v___x_4335_, 0);
                        lean_dec(v_unused_4343_);
                        v___x_4337_ = v___x_4335_;
                        v_isShared_4338_ = v_isSharedCheck_4342_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v___x_4335_);
                        v___x_4337_ = lean_box(0);
                        v_isShared_4338_ = v_isSharedCheck_4342_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___x_4335_;
                }
            }
            5 => {
                if v_isShared_4338_ == 0 {
                    lean_ctor_set(v___x_4337_, 0, v_a_4334_);
                    v___x_4340_ = v___x_4337_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4334_);
                    v___x_4340_ = v_reuseFailAlloc_4341_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4340_;
            }
            7 => {
                if lean_obj_tag(v___y_4345_) == 0 {
                    v_a_4346_ = lean_ctor_get(v___y_4345_, 0);
                    lean_inc(v_a_4346_);
                    lean_dec_ref_known(v___y_4345_, 1);
                    v_a_4334_ = v_a_4346_;
                    state = 4;
                    continue;
                } else {
                    v_a_4347_ = lean_ctor_get(v___y_4345_, 0);
                    lean_inc(v_a_4347_);
                    lean_dec_ref_known(v___y_4345_, 1);
                    v_a_4323_ = v_a_4347_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                if v_isShared_4371_ == 0 {
                    v___x_4373_ = v___x_4370_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
                    v___x_4373_ = v_reuseFailAlloc_4374_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___boxed(
    mut v_initialState_4376_: *mut LeanObject,
    mut v_tac_4377_: *mut LeanObject,
    mut v_expectedType_x3f_4378_: *mut LeanObject,
    mut v_a_4379_: *mut LeanObject,
    mut v_a_4380_: *mut LeanObject,
    mut v_a_4381_: *mut LeanObject,
    mut v_a_4382_: *mut LeanObject,
    mut v_a_4383_: *mut LeanObject,
    mut v_a_4384_: *mut LeanObject,
    mut v_a_4385_: *mut LeanObject,
    mut v_a_4386_: *mut LeanObject,
    mut v_a_4387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4388_: *mut LeanObject = core::ptr::null_mut();
    v_res_4388_ =
        l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(
            v_initialState_4376_,
            v_tac_4377_,
            v_expectedType_x3f_4378_,
            v_a_4379_,
            v_a_4380_,
            v_a_4381_,
            v_a_4382_,
            v_a_4383_,
            v_a_4384_,
            v_a_4385_,
            v_a_4386_,
        );
    lean_dec(v_a_4386_);
    lean_dec_ref(v_a_4385_);
    lean_dec(v_a_4384_);
    lean_dec_ref(v_a_4383_);
    lean_dec(v_a_4382_);
    lean_dec_ref(v_a_4381_);
    lean_dec(v_a_4380_);
    lean_dec_ref(v_a_4379_);
    return v_res_4388_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2(
    mut v_00_u03b1_4389_: *mut LeanObject,
    mut v_msg_4390_: *mut LeanObject,
    mut v___y_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    v___x_4400_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_msg_4390_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
    return v___x_4400_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___boxed(
    mut v_00_u03b1_4401_: *mut LeanObject,
    mut v_msg_4402_: *mut LeanObject,
    mut v___y_4403_: *mut LeanObject,
    mut v___y_4404_: *mut LeanObject,
    mut v___y_4405_: *mut LeanObject,
    mut v___y_4406_: *mut LeanObject,
    mut v___y_4407_: *mut LeanObject,
    mut v___y_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
    mut v___y_4411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4412_: *mut LeanObject = core::ptr::null_mut();
    v_res_4412_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2(v_00_u03b1_4401_, v_msg_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
    lean_dec(v___y_4410_);
    lean_dec_ref(v___y_4409_);
    lean_dec(v___y_4408_);
    lean_dec_ref(v___y_4407_);
    lean_dec(v___y_4406_);
    lean_dec_ref(v___y_4405_);
    lean_dec(v___y_4404_);
    lean_dec_ref(v___y_4403_);
    return v_res_4412_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16()
-> *mut LeanObject {
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    v___x_4446_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15;
    v___x_4447_ = l_Lean_stringToMessageData(v___x_4446_);
    return v___x_4447_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17()
-> *mut LeanObject {
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    v___x_4448_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14;
    v___x_4449_ = l_Lean_stringToMessageData(v___x_4448_);
    return v___x_4449_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(
    mut v_tac_4450_: *mut LeanObject,
    mut v_msg_4451_: *mut LeanObject,
    mut v_initialState_4452_: *mut LeanObject,
    mut v_expectedType_x3f_4453_: *mut LeanObject,
    mut v_a_4454_: *mut LeanObject,
    mut v_a_4455_: *mut LeanObject,
    mut v_a_4456_: *mut LeanObject,
    mut v_a_4457_: *mut LeanObject,
    mut v_a_4458_: *mut LeanObject,
    mut v_a_4459_: *mut LeanObject,
    mut v_a_4460_: *mut LeanObject,
    mut v_a_4461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4466_: u8 = 0;
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4470_: u8 = 0;
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v_unused_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4480_: u8 = 0;
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4497_: u8 = 0;
    let mut v_unused_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___y_4504_: u8 = 0;
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4531_: u8 = 0;
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4541_: u8 = 0;
    let mut v_unused_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: u8 = 0;
    let mut v___x_4545_: u8 = 0;
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
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: u8 = 0;
    let mut v___x_4566_: u8 = 0;
    let mut v_isSharedCheck_4567_: u8 = 0;
    let mut v_a_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4571_: u8 = 0;
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4575_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4486_ = l_Lean_Elab_Tactic_saveState___redArg(
                    v_a_4455_, v_a_4457_, v_a_4459_, v_a_4461_,
                );
                if lean_obj_tag(v___x_4486_) == 0 {
                    v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
                    lean_inc(v_a_4487_);
                    lean_dec_ref_known(v___x_4486_, 1);
                    lean_inc(v_expectedType_x3f_4453_);
                    lean_inc(v_tac_4450_);
                    lean_inc_ref(v_initialState_4452_);
                    v___x_4488_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_4452_, v_tac_4450_, v_expectedType_x3f_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
                    if lean_obj_tag(v___x_4488_) == 0 {
                        lean_dec(v_a_4487_);
                        lean_dec(v_expectedType_x3f_4453_);
                        lean_dec_ref(v_initialState_4452_);
                        v_isSharedCheck_4497_ = (!lean_is_exclusive(v___x_4488_)) as u8;
                        if v_isSharedCheck_4497_ == 0 {
                            v_unused_4498_ = lean_ctor_get(v___x_4488_, 0);
                            lean_dec(v_unused_4498_);
                            v___x_4490_ = v___x_4488_;
                            v_isShared_4491_ = v_isSharedCheck_4497_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v___x_4488_);
                            v___x_4490_ = lean_box(0);
                            v_isShared_4491_ = v_isSharedCheck_4497_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4499_ = lean_ctor_get(v___x_4488_, 0);
                        v_isSharedCheck_4567_ = (!lean_is_exclusive(v___x_4488_)) as u8;
                        if v_isSharedCheck_4567_ == 0 {
                            v___x_4501_ = v___x_4488_;
                            v_isShared_4502_ = v_isSharedCheck_4567_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_4499_);
                            lean_dec(v___x_4488_);
                            v___x_4501_ = lean_box(0);
                            v_isShared_4502_ = v_isSharedCheck_4567_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_expectedType_x3f_4453_);
                    lean_dec_ref(v_initialState_4452_);
                    lean_dec_ref(v_msg_4451_);
                    lean_dec(v_tac_4450_);
                    v_a_4568_ = lean_ctor_get(v___x_4486_, 0);
                    v_isSharedCheck_4575_ = (!lean_is_exclusive(v___x_4486_)) as u8;
                    if v_isSharedCheck_4575_ == 0 {
                        v___x_4570_ = v___x_4486_;
                        v_isShared_4571_ = v_isSharedCheck_4575_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_4568_);
                        lean_dec(v___x_4486_);
                        v___x_4570_ = lean_box(0);
                        v_isShared_4571_ = v_isSharedCheck_4575_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_4466_ == 0 {
                    lean_dec_ref(v___y_4465_);
                    v___x_4467_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v___y_4464_,
                        v___y_4466_,
                        v_a_4455_,
                        v_a_4456_,
                        v_a_4457_,
                        v_a_4458_,
                        v_a_4459_,
                        v_a_4460_,
                        v_a_4461_,
                    );
                    if lean_obj_tag(v___x_4467_) == 0 {
                        v_isSharedCheck_4475_ = (!lean_is_exclusive(v___x_4467_)) as u8;
                        if v_isSharedCheck_4475_ == 0 {
                            v_unused_4476_ = lean_ctor_get(v___x_4467_, 0);
                            lean_dec(v_unused_4476_);
                            v___x_4469_ = v___x_4467_;
                            v_isShared_4470_ = v_isSharedCheck_4475_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_4467_);
                            v___x_4469_ = lean_box(0);
                            v_isShared_4470_ = v_isSharedCheck_4475_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_4477_ = lean_ctor_get(v___x_4467_, 0);
                        v_isSharedCheck_4484_ = (!lean_is_exclusive(v___x_4467_)) as u8;
                        if v_isSharedCheck_4484_ == 0 {
                            v___x_4479_ = v___x_4467_;
                            v_isShared_4480_ = v_isSharedCheck_4484_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4477_);
                            lean_dec(v___x_4467_);
                            v___x_4479_ = lean_box(0);
                            v_isShared_4480_ = v_isSharedCheck_4484_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_4464_);
                    v___x_4485_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4485_, 0, v___y_4465_);
                    return v___x_4485_;
                }
            }
            2 => {
                v___x_4471_ = lean_box(0);
                if v_isShared_4470_ == 0 {
                    lean_ctor_set(v___x_4469_, 0, v___x_4471_);
                    v___x_4473_ = v___x_4469_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4471_);
                    v___x_4473_ = v_reuseFailAlloc_4474_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4473_;
            }
            4 => {
                if v_isShared_4480_ == 0 {
                    v___x_4482_ = v___x_4479_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
                    v___x_4482_ = v_reuseFailAlloc_4483_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4482_;
            }
            6 => {
                v___x_4492_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4492_, 0, v_tac_4450_);
                lean_ctor_set(v___x_4492_, 1, v_msg_4451_);
                v___x_4493_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4493_, 0, v___x_4492_);
                if v_isShared_4491_ == 0 {
                    lean_ctor_set(v___x_4490_, 0, v___x_4493_);
                    v___x_4495_ = v___x_4490_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4493_);
                    v___x_4495_ = v_reuseFailAlloc_4496_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4495_;
            }
            8 => {
                v___x_4565_ = l_Lean_Exception_isInterrupt(v_a_4499_);
                if v___x_4565_ == 0 {
                    lean_inc(v_a_4499_);
                    v___x_4566_ = l_Lean_Exception_isRuntime(v_a_4499_);
                    v___y_4504_ = v___x_4566_;
                    state = 9;
                    continue;
                } else {
                    v___y_4504_ = v___x_4565_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v___y_4504_ == 0 {
                    lean_del_object(v___x_4501_);
                    lean_dec(v_a_4499_);
                    v___x_4505_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v_a_4487_,
                        v___y_4504_,
                        v_a_4455_,
                        v_a_4456_,
                        v_a_4457_,
                        v_a_4458_,
                        v_a_4459_,
                        v_a_4460_,
                        v_a_4461_,
                    );
                    if lean_obj_tag(v___x_4505_) == 0 {
                        lean_dec_ref_known(v___x_4505_, 1);
                        v_ref_4506_ = lean_ctor_get(v_a_4460_, 5);
                        v___x_4507_ = l_Lean_SourceInfo_fromRef(v_ref_4506_, v___y_4504_);
                        v___x_4508_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2;
                        v___x_4509_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3;
                        lean_inc_n(v___x_4507_, 6);
                        v___x_4510_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_4510_, 0, v___x_4507_);
                        lean_ctor_set(v___x_4510_, 1, v___x_4509_);
                        v___x_4511_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5;
                        v___x_4512_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7;
                        v___x_4513_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
                        v___x_4514_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11;
                        v___x_4515_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12;
                        v___x_4516_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_4516_, 0, v___x_4507_);
                        lean_ctor_set(v___x_4516_, 1, v___x_4515_);
                        v___x_4517_ = l_Lean_Syntax_node1(v___x_4507_, v___x_4514_, v___x_4516_);
                        v___x_4518_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13;
                        v___x_4519_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_4519_, 0, v___x_4507_);
                        lean_ctor_set(v___x_4519_, 1, v___x_4518_);
                        v___x_4520_ = l_Lean_Syntax_node3(
                            v___x_4507_,
                            v___x_4513_,
                            v___x_4517_,
                            v___x_4519_,
                            v_tac_4450_,
                        );
                        v___x_4521_ = l_Lean_Syntax_node1(v___x_4507_, v___x_4512_, v___x_4520_);
                        v___x_4522_ = l_Lean_Elab_Tactic_saveState___redArg(
                            v_a_4455_, v_a_4457_, v_a_4459_, v_a_4461_,
                        );
                        if lean_obj_tag(v___x_4522_) == 0 {
                            v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
                            lean_inc(v_a_4523_);
                            lean_dec_ref_known(v___x_4522_, 1);
                            lean_inc_n(v___x_4507_, 2);
                            v___x_4524_ =
                                l_Lean_Syntax_node1(v___x_4507_, v___x_4511_, v___x_4521_);
                            v___x_4525_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14;
                            v___x_4526_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4526_, 0, v___x_4507_);
                            lean_ctor_set(v___x_4526_, 1, v___x_4525_);
                            v___x_4527_ = l_Lean_Syntax_node3(
                                v___x_4507_,
                                v___x_4508_,
                                v___x_4510_,
                                v___x_4524_,
                                v___x_4526_,
                            );
                            lean_inc(v___x_4527_);
                            v___x_4528_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_4452_, v___x_4527_, v_expectedType_x3f_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
                            if lean_obj_tag(v___x_4528_) == 0 {
                                lean_dec(v_a_4523_);
                                v_isSharedCheck_4541_ = (!lean_is_exclusive(v___x_4528_)) as u8;
                                if v_isSharedCheck_4541_ == 0 {
                                    v_unused_4542_ = lean_ctor_get(v___x_4528_, 0);
                                    lean_dec(v_unused_4542_);
                                    v___x_4530_ = v___x_4528_;
                                    v_isShared_4531_ = v_isSharedCheck_4541_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_dec(v___x_4528_);
                                    v___x_4530_ = lean_box(0);
                                    v_isShared_4531_ = v_isSharedCheck_4541_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_4527_);
                                lean_dec_ref(v_msg_4451_);
                                v_a_4543_ = lean_ctor_get(v___x_4528_, 0);
                                lean_inc(v_a_4543_);
                                lean_dec_ref_known(v___x_4528_, 1);
                                v___x_4544_ = l_Lean_Exception_isInterrupt(v_a_4543_);
                                if v___x_4544_ == 0 {
                                    lean_inc(v_a_4543_);
                                    v___x_4545_ = l_Lean_Exception_isRuntime(v_a_4543_);
                                    v___y_4464_ = v_a_4523_;
                                    v___y_4465_ = v_a_4543_;
                                    v___y_4466_ = v___x_4545_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___y_4464_ = v_a_4523_;
                                    v___y_4465_ = v_a_4543_;
                                    v___y_4466_ = v___x_4544_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_4521_);
                            lean_dec_ref_known(v___x_4510_, 2);
                            lean_dec(v___x_4507_);
                            lean_dec(v_expectedType_x3f_4453_);
                            lean_dec_ref(v_initialState_4452_);
                            lean_dec_ref(v_msg_4451_);
                            v_a_4546_ = lean_ctor_get(v___x_4522_, 0);
                            v_isSharedCheck_4553_ = (!lean_is_exclusive(v___x_4522_)) as u8;
                            if v_isSharedCheck_4553_ == 0 {
                                v___x_4548_ = v___x_4522_;
                                v_isShared_4549_ = v_isSharedCheck_4553_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_4546_);
                                lean_dec(v___x_4522_);
                                v___x_4548_ = lean_box(0);
                                v_isShared_4549_ = v_isSharedCheck_4553_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_expectedType_x3f_4453_);
                        lean_dec_ref(v_initialState_4452_);
                        lean_dec_ref(v_msg_4451_);
                        lean_dec(v_tac_4450_);
                        v_a_4554_ = lean_ctor_get(v___x_4505_, 0);
                        v_isSharedCheck_4561_ = (!lean_is_exclusive(v___x_4505_)) as u8;
                        if v_isSharedCheck_4561_ == 0 {
                            v___x_4556_ = v___x_4505_;
                            v_isShared_4557_ = v_isSharedCheck_4561_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_4554_);
                            lean_dec(v___x_4505_);
                            v___x_4556_ = lean_box(0);
                            v_isShared_4557_ = v_isSharedCheck_4561_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4487_);
                    lean_dec(v_expectedType_x3f_4453_);
                    lean_dec_ref(v_initialState_4452_);
                    lean_dec_ref(v_msg_4451_);
                    lean_dec(v_tac_4450_);
                    if v_isShared_4502_ == 0 {
                        v___x_4563_ = v___x_4501_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_4564_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4499_);
                        v___x_4563_ = v_reuseFailAlloc_4564_;
                        state = 16;
                        continue;
                    }
                }
            }
            10 => {
                v___x_4532_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
                v___x_4533_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4533_, 0, v___x_4532_);
                lean_ctor_set(v___x_4533_, 1, v_msg_4451_);
                v___x_4534_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
                v___x_4535_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4535_, 0, v___x_4533_);
                lean_ctor_set(v___x_4535_, 1, v___x_4534_);
                v___x_4536_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4536_, 0, v___x_4527_);
                lean_ctor_set(v___x_4536_, 1, v___x_4535_);
                v___x_4537_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4537_, 0, v___x_4536_);
                if v_isShared_4531_ == 0 {
                    lean_ctor_set(v___x_4530_, 0, v___x_4537_);
                    v___x_4539_ = v___x_4530_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4540_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4540_, 0, v___x_4537_);
                    v___x_4539_ = v_reuseFailAlloc_4540_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4539_;
            }
            12 => {
                if v_isShared_4549_ == 0 {
                    v___x_4551_ = v___x_4548_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
                    v___x_4551_ = v_reuseFailAlloc_4552_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4551_;
            }
            14 => {
                if v_isShared_4557_ == 0 {
                    v___x_4559_ = v___x_4556_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
                    v___x_4559_ = v_reuseFailAlloc_4560_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4559_;
            }
            16 => {
                return v___x_4563_;
            }
            17 => {
                if v_isShared_4571_ == 0 {
                    v___x_4573_ = v___x_4570_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
                    v___x_4573_ = v_reuseFailAlloc_4574_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4573_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___boxed(
    mut v_tac_4576_: *mut LeanObject,
    mut v_msg_4577_: *mut LeanObject,
    mut v_initialState_4578_: *mut LeanObject,
    mut v_expectedType_x3f_4579_: *mut LeanObject,
    mut v_a_4580_: *mut LeanObject,
    mut v_a_4581_: *mut LeanObject,
    mut v_a_4582_: *mut LeanObject,
    mut v_a_4583_: *mut LeanObject,
    mut v_a_4584_: *mut LeanObject,
    mut v_a_4585_: *mut LeanObject,
    mut v_a_4586_: *mut LeanObject,
    mut v_a_4587_: *mut LeanObject,
    mut v_a_4588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4589_: *mut LeanObject = core::ptr::null_mut();
    v_res_4589_ =
        l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(
            v_tac_4576_,
            v_msg_4577_,
            v_initialState_4578_,
            v_expectedType_x3f_4579_,
            v_a_4580_,
            v_a_4581_,
            v_a_4582_,
            v_a_4583_,
            v_a_4584_,
            v_a_4585_,
            v_a_4586_,
            v_a_4587_,
        );
    lean_dec(v_a_4587_);
    lean_dec_ref(v_a_4586_);
    lean_dec(v_a_4585_);
    lean_dec_ref(v_a_4584_);
    lean_dec(v_a_4583_);
    lean_dec_ref(v_a_4582_);
    lean_dec(v_a_4581_);
    lean_dec_ref(v_a_4580_);
    return v_res_4589_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1()
-> *mut LeanObject {
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    v___x_4591_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__0;
    v___x_4592_ = l_Lean_stringToMessageData(v___x_4591_);
    return v___x_4592_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3()
-> *mut LeanObject {
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    v___x_4594_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2;
    v___x_4595_ = l_Lean_stringToMessageData(v___x_4594_);
    return v___x_4595_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5()
-> *mut LeanObject {
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    v___x_4597_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4;
    v___x_4598_ = l_Lean_stringToMessageData(v___x_4597_);
    return v___x_4598_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(
    mut v_targetKind_4599_: *mut LeanObject,
    mut v_invalidTactic_4600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    v___x_4601_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1);
    v___x_4602_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4602_, 0, v___x_4601_);
    lean_ctor_set(v___x_4602_, 1, v_targetKind_4599_);
    v___x_4603_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3);
    v___x_4604_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4604_, 0, v___x_4602_);
    lean_ctor_set(v___x_4604_, 1, v___x_4603_);
    v___x_4605_ = l_Lean_indentD(v_invalidTactic_4600_);
    v___x_4606_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4606_, 0, v___x_4604_);
    lean_ctor_set(v___x_4606_, 1, v___x_4605_);
    v___x_4607_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5);
    v___x_4608_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4608_, 0, v___x_4606_);
    lean_ctor_set(v___x_4608_, 1, v___x_4607_);
    return v___x_4608_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    v___x_4610_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__0;
    v___x_4611_ = l_Lean_stringToMessageData(v___x_4610_);
    return v___x_4611_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    v___x_4613_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__2;
    v___x_4614_ = l_Lean_stringToMessageData(v___x_4613_);
    return v___x_4614_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(
    mut v_e_4627_: *mut LeanObject,
    mut v_useRefine_4628_: u8,
    mut v___y_4629_: *mut LeanObject,
    mut v___y_4630_: *mut LeanObject,
    mut v___y_4631_: *mut LeanObject,
    mut v___y_4632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tac_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: u8 = 0;
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4671_: u8 = 0;
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_4627_);
                v___x_4639_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(
                    v_e_4627_,
                    v___y_4629_,
                    v___y_4630_,
                    v___y_4631_,
                    v___y_4632_,
                );
                if lean_obj_tag(v___x_4639_) == 0 {
                    v_a_4640_ = lean_ctor_get(v___x_4639_, 0);
                    lean_inc(v_a_4640_);
                    lean_dec_ref_known(v___x_4639_, 1);
                    if v_useRefine_4628_ == 0 {
                        v_ref_4655_ = lean_ctor_get(v___y_4631_, 5);
                        v___x_4656_ = l_Lean_SourceInfo_fromRef(v_ref_4655_, v_useRefine_4628_);
                        v___x_4657_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4;
                        v___x_4658_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5;
                        lean_inc(v___x_4656_);
                        v___x_4659_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_4659_, 0, v___x_4656_);
                        lean_ctor_set(v___x_4659_, 1, v___x_4657_);
                        v___x_4660_ =
                            l_Lean_Syntax_node2(v___x_4656_, v___x_4658_, v___x_4659_, v_a_4640_);
                        v_tac_4642_ = v___x_4660_;
                        v___y_4643_ = v___y_4629_;
                        v___y_4644_ = v___y_4630_;
                        v___y_4645_ = v___y_4631_;
                        v___y_4646_ = v___y_4632_;
                        state = 2;
                        continue;
                    } else {
                        v_ref_4661_ = lean_ctor_get(v___y_4631_, 5);
                        v___x_4662_ = 0;
                        v___x_4663_ = l_Lean_SourceInfo_fromRef(v_ref_4661_, v___x_4662_);
                        v___x_4664_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6;
                        v___x_4665_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7;
                        lean_inc(v___x_4663_);
                        v___x_4666_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_4666_, 0, v___x_4663_);
                        lean_ctor_set(v___x_4666_, 1, v___x_4664_);
                        v___x_4667_ =
                            l_Lean_Syntax_node2(v___x_4663_, v___x_4665_, v___x_4666_, v_a_4640_);
                        v_tac_4642_ = v___x_4667_;
                        v___y_4643_ = v___y_4629_;
                        v___y_4644_ = v___y_4630_;
                        v___y_4645_ = v___y_4631_;
                        v___y_4646_ = v___y_4632_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_4627_);
                    v_a_4668_ = lean_ctor_get(v___x_4639_, 0);
                    v_isSharedCheck_4675_ = (!lean_is_exclusive(v___x_4639_)) as u8;
                    if v_isSharedCheck_4675_ == 0 {
                        v___x_4670_ = v___x_4639_;
                        v_isShared_4671_ = v_isSharedCheck_4675_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4668_);
                        lean_dec(v___x_4639_);
                        v___x_4670_ = lean_box(0);
                        v_isShared_4671_ = v_isSharedCheck_4675_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4637_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4637_, 0, v___y_4635_);
                lean_ctor_set(v___x_4637_, 1, v___y_4636_);
                v___x_4638_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4638_, 0, v___x_4637_);
                return v___x_4638_;
            }
            2 => {
                v___x_4647_ = l_Lean_MessageData_ofExpr(v_e_4627_);
                v___x_4648_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_4647_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
                if v_useRefine_4628_ == 0 {
                    v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
                    lean_inc(v_a_4649_);
                    lean_dec_ref(v___x_4648_);
                    v___x_4650_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1);
                    v___x_4651_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4651_, 0, v___x_4650_);
                    lean_ctor_set(v___x_4651_, 1, v_a_4649_);
                    v___y_4635_ = v_tac_4642_;
                    v___y_4636_ = v___x_4651_;
                    state = 1;
                    continue;
                } else {
                    v_a_4652_ = lean_ctor_get(v___x_4648_, 0);
                    lean_inc(v_a_4652_);
                    lean_dec_ref(v___x_4648_);
                    v___x_4653_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3);
                    v___x_4654_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4654_, 0, v___x_4653_);
                    lean_ctor_set(v___x_4654_, 1, v_a_4652_);
                    v___y_4635_ = v_tac_4642_;
                    v___y_4636_ = v___x_4654_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_4671_ == 0 {
                    v___x_4673_ = v___x_4670_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
                    v___x_4673_ = v_reuseFailAlloc_4674_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed(
    mut v_e_4676_: *mut LeanObject,
    mut v_useRefine_4677_: *mut LeanObject,
    mut v___y_4678_: *mut LeanObject,
    mut v___y_4679_: *mut LeanObject,
    mut v___y_4680_: *mut LeanObject,
    mut v___y_4681_: *mut LeanObject,
    mut v___y_4682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useRefine_boxed_4683_: u8 = 0;
    let mut v_res_4684_: *mut LeanObject = core::ptr::null_mut();
    v_useRefine_boxed_4683_ = (lean_unbox(v_useRefine_4677_) as u8);
    v_res_4684_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(v_e_4676_, v_useRefine_boxed_4683_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
    lean_dec(v___y_4681_);
    lean_dec_ref(v___y_4680_);
    lean_dec(v___y_4679_);
    lean_dec_ref(v___y_4678_);
    return v_res_4684_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(
    mut v_e_4685_: *mut LeanObject,
    mut v_useRefine_4686_: u8,
    mut v_a_4687_: *mut LeanObject,
    mut v_a_4688_: *mut LeanObject,
    mut v_a_4689_: *mut LeanObject,
    mut v_a_4690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4705_: u8 = 0;
    let mut v_inheritedTraceOptions_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: u8 = 0;
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: u8 = 0;
    let mut v_fileName_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4727_: u8 = 0;
    let mut v_inheritedTraceOptions_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4735_: u8 = 0;
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4747_: u8 = 0;
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4754_: u8 = 0;
    let mut v_unused_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4692_ = lean_st_ref_get(v_a_4690_);
                v_fileName_4693_ = lean_ctor_get(v_a_4689_, 0);
                v_fileMap_4694_ = lean_ctor_get(v_a_4689_, 1);
                v_options_4695_ = lean_ctor_get(v_a_4689_, 2);
                v_currRecDepth_4696_ = lean_ctor_get(v_a_4689_, 3);
                v_ref_4697_ = lean_ctor_get(v_a_4689_, 5);
                v_currNamespace_4698_ = lean_ctor_get(v_a_4689_, 6);
                v_openDecls_4699_ = lean_ctor_get(v_a_4689_, 7);
                v_initHeartbeats_4700_ = lean_ctor_get(v_a_4689_, 8);
                v_maxHeartbeats_4701_ = lean_ctor_get(v_a_4689_, 9);
                v_quotContext_4702_ = lean_ctor_get(v_a_4689_, 10);
                v_currMacroScope_4703_ = lean_ctor_get(v_a_4689_, 11);
                v_cancelTk_x3f_4704_ = lean_ctor_get(v_a_4689_, 12);
                v_suppressElabErrors_4705_ = lean_ctor_get_uint8(
                    v_a_4689_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4706_ = lean_ctor_get(v_a_4689_, 13);
                v_env_4707_ = lean_ctor_get(v___x_4692_, 0);
                lean_inc_ref(v_env_4707_);
                lean_dec(v___x_4692_);
                v___x_4708_ = lean_box((v_useRefine_4686_) as usize);
                v___f_4709_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
                lean_closure_set(v___f_4709_, 0, v_e_4685_);
                lean_closure_set(v___f_4709_, 1, v___x_4708_);
                v___x_4710_ = l_Lean_pp_mvars;
                v___x_4711_ = 0;
                lean_inc_ref(v_options_4695_);
                v___x_4712_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_options_4695_, v___x_4710_, v___x_4711_);
                v___x_4713_ = l_Lean_diagnostics;
                v___x_4714_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v___x_4712_, v___x_4713_);
                v___x_4756_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4707_);
                lean_dec_ref(v_env_4707_);
                if v___x_4756_ == 0 {
                    if v___x_4714_ == 0 {
                        v_fileName_4716_ = v_fileName_4693_;
                        v_fileMap_4717_ = v_fileMap_4694_;
                        v_currRecDepth_4718_ = v_currRecDepth_4696_;
                        v_ref_4719_ = v_ref_4697_;
                        v_currNamespace_4720_ = v_currNamespace_4698_;
                        v_openDecls_4721_ = v_openDecls_4699_;
                        v_initHeartbeats_4722_ = v_initHeartbeats_4700_;
                        v_maxHeartbeats_4723_ = v_maxHeartbeats_4701_;
                        v_quotContext_4724_ = v_quotContext_4702_;
                        v_currMacroScope_4725_ = v_currMacroScope_4703_;
                        v_cancelTk_x3f_4726_ = v_cancelTk_x3f_4704_;
                        v_suppressElabErrors_4727_ = v_suppressElabErrors_4705_;
                        v_inheritedTraceOptions_4728_ = v_inheritedTraceOptions_4706_;
                        v___y_4729_ = v_a_4690_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4735_ = v___x_4756_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___y_4735_ = v___x_4714_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4730_ = l_Lean_maxRecDepth;
                v___x_4731_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(v___x_4712_, v___x_4730_);
                lean_inc_ref(v_inheritedTraceOptions_4728_);
                lean_inc(v_cancelTk_x3f_4726_);
                lean_inc(v_currMacroScope_4725_);
                lean_inc(v_quotContext_4724_);
                lean_inc(v_maxHeartbeats_4723_);
                lean_inc(v_initHeartbeats_4722_);
                lean_inc(v_openDecls_4721_);
                lean_inc(v_currNamespace_4720_);
                lean_inc(v_ref_4719_);
                lean_inc(v_currRecDepth_4718_);
                lean_inc_ref(v_fileMap_4717_);
                lean_inc_ref(v_fileName_4716_);
                v___x_4732_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4732_, 0, v_fileName_4716_);
                lean_ctor_set(v___x_4732_, 1, v_fileMap_4717_);
                lean_ctor_set(v___x_4732_, 2, v___x_4712_);
                lean_ctor_set(v___x_4732_, 3, v_currRecDepth_4718_);
                lean_ctor_set(v___x_4732_, 4, v___x_4731_);
                lean_ctor_set(v___x_4732_, 5, v_ref_4719_);
                lean_ctor_set(v___x_4732_, 6, v_currNamespace_4720_);
                lean_ctor_set(v___x_4732_, 7, v_openDecls_4721_);
                lean_ctor_set(v___x_4732_, 8, v_initHeartbeats_4722_);
                lean_ctor_set(v___x_4732_, 9, v_maxHeartbeats_4723_);
                lean_ctor_set(v___x_4732_, 10, v_quotContext_4724_);
                lean_ctor_set(v___x_4732_, 11, v_currMacroScope_4725_);
                lean_ctor_set(v___x_4732_, 12, v_cancelTk_x3f_4726_);
                lean_ctor_set(v___x_4732_, 13, v_inheritedTraceOptions_4728_);
                lean_ctor_set_uint8(
                    v___x_4732_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_4714_,
                );
                lean_ctor_set_uint8(
                    v___x_4732_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4727_,
                );
                v___x_4733_ = l_Lean_Meta_withExposedNames___redArg(
                    v___f_4709_,
                    v_a_4687_,
                    v_a_4688_,
                    v___x_4732_,
                    v___y_4729_,
                );
                lean_dec_ref_known(v___x_4732_, 14);
                return v___x_4733_;
            }
            2 => {
                if v___y_4735_ == 0 {
                    v___x_4736_ = lean_st_ref_take(v_a_4690_);
                    v_env_4737_ = lean_ctor_get(v___x_4736_, 0);
                    v_nextMacroScope_4738_ = lean_ctor_get(v___x_4736_, 1);
                    v_ngen_4739_ = lean_ctor_get(v___x_4736_, 2);
                    v_auxDeclNGen_4740_ = lean_ctor_get(v___x_4736_, 3);
                    v_traceState_4741_ = lean_ctor_get(v___x_4736_, 4);
                    v_messages_4742_ = lean_ctor_get(v___x_4736_, 6);
                    v_infoState_4743_ = lean_ctor_get(v___x_4736_, 7);
                    v_snapshotTasks_4744_ = lean_ctor_get(v___x_4736_, 8);
                    v_isSharedCheck_4754_ = (!lean_is_exclusive(v___x_4736_)) as u8;
                    if v_isSharedCheck_4754_ == 0 {
                        v_unused_4755_ = lean_ctor_get(v___x_4736_, 5);
                        lean_dec(v_unused_4755_);
                        v___x_4746_ = v___x_4736_;
                        v_isShared_4747_ = v_isSharedCheck_4754_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_4744_);
                        lean_inc(v_infoState_4743_);
                        lean_inc(v_messages_4742_);
                        lean_inc(v_traceState_4741_);
                        lean_inc(v_auxDeclNGen_4740_);
                        lean_inc(v_ngen_4739_);
                        lean_inc(v_nextMacroScope_4738_);
                        lean_inc(v_env_4737_);
                        lean_dec(v___x_4736_);
                        v___x_4746_ = lean_box(0);
                        v_isShared_4747_ = v_isSharedCheck_4754_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_fileName_4716_ = v_fileName_4693_;
                    v_fileMap_4717_ = v_fileMap_4694_;
                    v_currRecDepth_4718_ = v_currRecDepth_4696_;
                    v_ref_4719_ = v_ref_4697_;
                    v_currNamespace_4720_ = v_currNamespace_4698_;
                    v_openDecls_4721_ = v_openDecls_4699_;
                    v_initHeartbeats_4722_ = v_initHeartbeats_4700_;
                    v_maxHeartbeats_4723_ = v_maxHeartbeats_4701_;
                    v_quotContext_4724_ = v_quotContext_4702_;
                    v_currMacroScope_4725_ = v_currMacroScope_4703_;
                    v_cancelTk_x3f_4726_ = v_cancelTk_x3f_4704_;
                    v_suppressElabErrors_4727_ = v_suppressElabErrors_4705_;
                    v_inheritedTraceOptions_4728_ = v_inheritedTraceOptions_4706_;
                    v___y_4729_ = v_a_4690_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4748_ = l_Lean_Kernel_enableDiag(v_env_4737_, v___x_4714_);
                v___x_4749_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2,
                );
                if v_isShared_4747_ == 0 {
                    lean_ctor_set(v___x_4746_, 5, v___x_4749_);
                    lean_ctor_set(v___x_4746_, 0, v___x_4748_);
                    v___x_4751_ = v___x_4746_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4748_);
                    lean_ctor_set(v_reuseFailAlloc_4753_, 1, v_nextMacroScope_4738_);
                    lean_ctor_set(v_reuseFailAlloc_4753_, 2, v_ngen_4739_);
                    lean_ctor_set(v_reuseFailAlloc_4753_, 3, v_auxDeclNGen_4740_);
                    lean_ctor_set(v_reuseFailAlloc_4753_, 4, v_traceState_4741_);
                    lean_ctor_set(v_reuseFailAlloc_4753_, 5, v___x_4749_);
                    lean_ctor_set(v_reuseFailAlloc_4753_, 6, v_messages_4742_);
                    lean_ctor_set(v_reuseFailAlloc_4753_, 7, v_infoState_4743_);
                    lean_ctor_set(v_reuseFailAlloc_4753_, 8, v_snapshotTasks_4744_);
                    v___x_4751_ = v_reuseFailAlloc_4753_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4752_ = lean_st_ref_set(v_a_4690_, v___x_4751_);
                v_fileName_4716_ = v_fileName_4693_;
                v_fileMap_4717_ = v_fileMap_4694_;
                v_currRecDepth_4718_ = v_currRecDepth_4696_;
                v_ref_4719_ = v_ref_4697_;
                v_currNamespace_4720_ = v_currNamespace_4698_;
                v_openDecls_4721_ = v_openDecls_4699_;
                v_initHeartbeats_4722_ = v_initHeartbeats_4700_;
                v_maxHeartbeats_4723_ = v_maxHeartbeats_4701_;
                v_quotContext_4724_ = v_quotContext_4702_;
                v_currMacroScope_4725_ = v_currMacroScope_4703_;
                v_cancelTk_x3f_4726_ = v_cancelTk_x3f_4704_;
                v_suppressElabErrors_4727_ = v_suppressElabErrors_4705_;
                v_inheritedTraceOptions_4728_ = v_inheritedTraceOptions_4706_;
                v___y_4729_ = v_a_4690_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___boxed(
    mut v_e_4757_: *mut LeanObject,
    mut v_useRefine_4758_: *mut LeanObject,
    mut v_a_4759_: *mut LeanObject,
    mut v_a_4760_: *mut LeanObject,
    mut v_a_4761_: *mut LeanObject,
    mut v_a_4762_: *mut LeanObject,
    mut v_a_4763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useRefine_boxed_4764_: u8 = 0;
    let mut v_res_4765_: *mut LeanObject = core::ptr::null_mut();
    v_useRefine_boxed_4764_ = (lean_unbox(v_useRefine_4758_) as u8);
    v_res_4765_ =
        l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(
            v_e_4757_,
            v_useRefine_boxed_4764_,
            v_a_4759_,
            v_a_4760_,
            v_a_4761_,
            v_a_4762_,
        );
    lean_dec(v_a_4762_);
    lean_dec_ref(v_a_4761_);
    lean_dec(v_a_4760_);
    lean_dec_ref(v_a_4759_);
    return v_res_4765_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(
    mut v_as_4769_: *mut LeanObject,
    mut v_sz_4770_: usize,
    mut v_i_4771_: usize,
    mut v_b_4772_: *mut LeanObject,
    mut v___y_4773_: *mut LeanObject,
    mut v___y_4774_: *mut LeanObject,
    mut v___y_4775_: *mut LeanObject,
    mut v___y_4776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4778_: u8 = 0;
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: usize = 0;
    let mut v___x_4795_: usize = 0;
    let mut v_a_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4800_: u8 = 0;
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4804_: u8 = 0;
    let mut v_a_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4808_: u8 = 0;
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4812_: u8 = 0;
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
                v___x_4778_ = lean_usize_dec_lt(v_i_4771_, v_sz_4770_);
                if v___x_4778_ == 0 {
                    v___x_4779_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4779_, 0, v_b_4772_);
                    return v___x_4779_;
                } else {
                    v_a_4780_ = lean_array_uget_borrowed(v_as_4769_, v_i_4771_);
                    lean_inc(v_a_4780_);
                    v___x_4781_ = l_Lean_MVarId_getType(
                        v_a_4780_,
                        v___y_4773_,
                        v___y_4774_,
                        v___y_4775_,
                        v___y_4776_,
                    );
                    if lean_obj_tag(v___x_4781_) == 0 {
                        v_a_4782_ = lean_ctor_get(v___x_4781_, 0);
                        lean_inc(v_a_4782_);
                        lean_dec_ref_known(v___x_4781_, 1);
                        v___x_4783_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_a_4782_, v___y_4774_);
                        if lean_obj_tag(v___x_4783_) == 0 {
                            v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
                            lean_inc(v_a_4784_);
                            lean_dec_ref_known(v___x_4783_, 1);
                            v___x_4785_ = lean_alloc_closure(
                                l_Lean_PrettyPrinter_ppExpr___boxed as *mut core::ffi::c_void,
                                6,
                                1,
                            );
                            lean_closure_set(v___x_4785_, 0, v_a_4784_);
                            v___x_4786_ = l_Lean_Meta_withExposedNames___redArg(
                                v___x_4785_,
                                v___y_4773_,
                                v___y_4774_,
                                v___y_4775_,
                                v___y_4776_,
                            );
                            if lean_obj_tag(v___x_4786_) == 0 {
                                v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
                                lean_inc(v_a_4787_);
                                lean_dec_ref_known(v___x_4786_, 1);
                                v___x_4788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__1;
                                v___x_4789_ = lean_alloc_ctor(5, 2, (0) as u32);
                                lean_ctor_set(v___x_4789_, 0, v___x_4788_);
                                lean_ctor_set(v___x_4789_, 1, v_a_4787_);
                                v___x_4790_ = l_Std_Format_defWidth;
                                v___x_4791_ = lean_unsigned_to_nat(0);
                                v___x_4792_ = l_Std_Format_pretty(
                                    v___x_4789_,
                                    v___x_4790_,
                                    v___x_4791_,
                                    v___x_4791_,
                                );
                                v___x_4793_ = lean_string_append(v_b_4772_, v___x_4792_);
                                lean_dec_ref(v___x_4792_);
                                v___x_4794_ = 1usize;
                                v___x_4795_ = lean_usize_add(v_i_4771_, v___x_4794_);
                                v_i_4771_ = v___x_4795_;
                                v_b_4772_ = v___x_4793_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec_ref(v_b_4772_);
                                v_a_4797_ = lean_ctor_get(v___x_4786_, 0);
                                v_isSharedCheck_4804_ = (!lean_is_exclusive(v___x_4786_)) as u8;
                                if v_isSharedCheck_4804_ == 0 {
                                    v___x_4799_ = v___x_4786_;
                                    v_isShared_4800_ = v_isSharedCheck_4804_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_4797_);
                                    lean_dec(v___x_4786_);
                                    v___x_4799_ = lean_box(0);
                                    v_isShared_4800_ = v_isSharedCheck_4804_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_b_4772_);
                            v_a_4805_ = lean_ctor_get(v___x_4783_, 0);
                            v_isSharedCheck_4812_ = (!lean_is_exclusive(v___x_4783_)) as u8;
                            if v_isSharedCheck_4812_ == 0 {
                                v___x_4807_ = v___x_4783_;
                                v_isShared_4808_ = v_isSharedCheck_4812_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4805_);
                                lean_dec(v___x_4783_);
                                v___x_4807_ = lean_box(0);
                                v_isShared_4808_ = v_isSharedCheck_4812_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_4772_);
                        v_a_4813_ = lean_ctor_get(v___x_4781_, 0);
                        v_isSharedCheck_4820_ = (!lean_is_exclusive(v___x_4781_)) as u8;
                        if v_isSharedCheck_4820_ == 0 {
                            v___x_4815_ = v___x_4781_;
                            v_isShared_4816_ = v_isSharedCheck_4820_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4813_);
                            lean_dec(v___x_4781_);
                            v___x_4815_ = lean_box(0);
                            v_isShared_4816_ = v_isSharedCheck_4820_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4800_ == 0 {
                    v___x_4802_ = v___x_4799_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4803_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_a_4797_);
                    v___x_4802_ = v_reuseFailAlloc_4803_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4802_;
            }
            3 => {
                if v_isShared_4808_ == 0 {
                    v___x_4810_ = v___x_4807_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
                    v___x_4810_ = v_reuseFailAlloc_4811_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4810_;
            }
            5 => {
                if v_isShared_4816_ == 0 {
                    v___x_4818_ = v___x_4815_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
                    v___x_4818_ = v_reuseFailAlloc_4819_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___boxed(
    mut v_as_4821_: *mut LeanObject,
    mut v_sz_4822_: *mut LeanObject,
    mut v_i_4823_: *mut LeanObject,
    mut v_b_4824_: *mut LeanObject,
    mut v___y_4825_: *mut LeanObject,
    mut v___y_4826_: *mut LeanObject,
    mut v___y_4827_: *mut LeanObject,
    mut v___y_4828_: *mut LeanObject,
    mut v___y_4829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4830_: usize = 0;
    let mut v_i_boxed_4831_: usize = 0;
    let mut v_res_4832_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4830_ = lean_unbox_usize(v_sz_4822_);
    lean_dec(v_sz_4822_);
    v_i_boxed_4831_ = lean_unbox_usize(v_i_4823_);
    lean_dec(v_i_4823_);
    v_res_4832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_4821_, v_sz_boxed_4830_, v_i_boxed_4831_, v_b_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_);
    lean_dec(v___y_4828_);
    lean_dec_ref(v___y_4827_);
    lean_dec(v___y_4826_);
    lean_dec_ref(v___y_4825_);
    lean_dec_ref(v_as_4821_);
    return v_res_4832_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3()
-> *mut LeanObject {
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    v___x_4837_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2;
    v___x_4838_ = l_Lean_stringToMessageData(v___x_4837_);
    return v___x_4838_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6()
-> *mut LeanObject {
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    v___x_4841_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__5;
    v___x_4842_ = l_Lean_stringToMessageData(v___x_4841_);
    return v___x_4842_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(
    mut v_addSubgoalsMsg_4844_: u8,
    mut v_checkState_x3f_4845_: *mut LeanObject,
    mut v_e_4846_: *mut LeanObject,
    mut v_a_4847_: *mut LeanObject,
    mut v_a_4848_: *mut LeanObject,
    mut v_a_4849_: *mut LeanObject,
    mut v_a_4850_: *mut LeanObject,
    mut v_a_4851_: *mut LeanObject,
    mut v_a_4852_: *mut LeanObject,
    mut v_a_4853_: *mut LeanObject,
    mut v_a_4854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postInfo_x3f_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4885_: u8 = 0;
    let mut v___y_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4887_: u8 = 0;
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4892_: u8 = 0;
    let mut v_fst_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4897_: u8 = 0;
    let mut v_val_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4905_: u8 = 0;
    let mut v_fst_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4911_: usize = 0;
    let mut v___x_4912_: usize = 0;
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4921_: u8 = 0;
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4925_: u8 = 0;
    let mut v_fst_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4928_: u8 = 0;
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4945_: u8 = 0;
    let mut v_isSharedCheck_4946_: u8 = 0;
    let mut v_fst_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4950_: u8 = 0;
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4961_: u8 = 0;
    let mut v_unused_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4963_: u8 = 0;
    let mut v_a_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4967_: u8 = 0;
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4971_: u8 = 0;
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4985_: u8 = 0;
    let mut v_inheritedTraceOptions_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: u8 = 0;
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: u8 = 0;
    let mut v_fileName_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5005_: u8 = 0;
    let mut v_inheritedTraceOptions_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: u8 = 0;
    let mut v___x_5016_: u8 = 0;
    let mut v_a_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5020_: u8 = 0;
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5024_: u8 = 0;
    let mut v___y_5026_: u8 = 0;
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5038_: u8 = 0;
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5045_: u8 = 0;
    let mut v_unused_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4972_ = lean_st_ref_get(v_a_4854_);
                v_fileName_4973_ = lean_ctor_get(v_a_4853_, 0);
                v_fileMap_4974_ = lean_ctor_get(v_a_4853_, 1);
                v_options_4975_ = lean_ctor_get(v_a_4853_, 2);
                v_currRecDepth_4976_ = lean_ctor_get(v_a_4853_, 3);
                v_ref_4977_ = lean_ctor_get(v_a_4853_, 5);
                v_currNamespace_4978_ = lean_ctor_get(v_a_4853_, 6);
                v_openDecls_4979_ = lean_ctor_get(v_a_4853_, 7);
                v_initHeartbeats_4980_ = lean_ctor_get(v_a_4853_, 8);
                v_maxHeartbeats_4981_ = lean_ctor_get(v_a_4853_, 9);
                v_quotContext_4982_ = lean_ctor_get(v_a_4853_, 10);
                v_currMacroScope_4983_ = lean_ctor_get(v_a_4853_, 11);
                v_cancelTk_x3f_4984_ = lean_ctor_get(v_a_4853_, 12);
                v_suppressElabErrors_4985_ = lean_ctor_get_uint8(
                    v_a_4853_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4986_ = lean_ctor_get(v_a_4853_, 13);
                v_env_4987_ = lean_ctor_get(v___x_4972_, 0);
                lean_inc_ref(v_env_4987_);
                lean_dec(v___x_4972_);
                v___x_4988_ = l_Lean_pp_mvars;
                v___x_4989_ = 0;
                lean_inc_ref(v_options_4975_);
                v___x_4990_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_options_4975_, v___x_4988_, v___x_4989_);
                v___x_4991_ = l_Lean_diagnostics;
                v___x_4992_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v___x_4990_, v___x_4991_);
                v___x_5047_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4987_);
                lean_dec_ref(v_env_4987_);
                if v___x_5047_ == 0 {
                    if v___x_4992_ == 0 {
                        v_fileName_4994_ = v_fileName_4973_;
                        v_fileMap_4995_ = v_fileMap_4974_;
                        v_currRecDepth_4996_ = v_currRecDepth_4976_;
                        v_ref_4997_ = v_ref_4977_;
                        v_currNamespace_4998_ = v_currNamespace_4978_;
                        v_openDecls_4999_ = v_openDecls_4979_;
                        v_initHeartbeats_5000_ = v_initHeartbeats_4980_;
                        v_maxHeartbeats_5001_ = v_maxHeartbeats_4981_;
                        v_quotContext_5002_ = v_quotContext_4982_;
                        v_currMacroScope_5003_ = v_currMacroScope_4983_;
                        v_cancelTk_x3f_5004_ = v_cancelTk_x3f_4984_;
                        v_suppressElabErrors_5005_ = v_suppressElabErrors_4985_;
                        v_inheritedTraceOptions_5006_ = v_inheritedTraceOptions_4986_;
                        v___y_5007_ = v_a_4854_;
                        state = 19;
                        continue;
                    } else {
                        v___y_5026_ = v___x_5047_;
                        state = 22;
                        continue;
                    }
                } else {
                    v___y_5026_ = v___x_4992_;
                    state = 22;
                    continue;
                }
            }
            1 => {
                v___x_4860_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1;
                v___x_4861_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4861_, 0, v___x_4860_);
                lean_ctor_set(v___x_4861_, 1, v___y_4858_);
                v___x_4862_ = lean_box(0);
                v___x_4863_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4863_, 0, v___y_4857_);
                v___x_4864_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_4864_, 0, v___x_4861_);
                lean_ctor_set(v___x_4864_, 1, v___x_4862_);
                lean_ctor_set(v___x_4864_, 2, v_postInfo_x3f_4859_);
                lean_ctor_set(v___x_4864_, 3, v___x_4862_);
                lean_ctor_set(v___x_4864_, 4, v___x_4863_);
                lean_ctor_set(v___x_4864_, 5, v___x_4862_);
                v___x_4865_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4865_, 0, v___x_4864_);
                v___x_4866_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4866_, 0, v___x_4865_);
                return v___x_4866_;
            }
            2 => {
                v___x_4870_ = lean_box(0);
                v___y_4857_ = v___y_4868_;
                v___y_4858_ = v___y_4869_;
                v_postInfo_x3f_4859_ = v___x_4870_;
                state = 1;
                continue;
            }
            3 => {
                lean_inc_ref(v___y_4874_);
                v___x_4875_ = l_Lean_stringToMessageData(v___y_4874_);
                lean_inc_ref(v___y_4873_);
                v___x_4876_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4876_, 0, v___y_4873_);
                lean_ctor_set(v___x_4876_, 1, v___x_4875_);
                v___x_4877_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3);
                v___x_4878_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4878_, 0, v___x_4876_);
                lean_ctor_set(v___x_4878_, 1, v___x_4877_);
                v___x_4879_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_4878_, v___y_4872_);
                v___x_4880_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4880_, 0, v___x_4879_);
                v___x_4881_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4881_, 0, v___x_4880_);
                return v___x_4881_;
            }
            4 => {
                v___x_4888_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(v_e_4846_, v___y_4887_, v_a_4851_, v_a_4852_, v___y_4886_, v___y_4884_);
                if lean_obj_tag(v___x_4888_) == 0 {
                    v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
                    v_isSharedCheck_4963_ = (!lean_is_exclusive(v___x_4888_)) as u8;
                    if v_isSharedCheck_4963_ == 0 {
                        v___x_4891_ = v___x_4888_;
                        v_isShared_4892_ = v_isSharedCheck_4963_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4889_);
                        lean_dec(v___x_4888_);
                        v___x_4891_ = lean_box(0);
                        v_isShared_4892_ = v_isSharedCheck_4963_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_4886_);
                    lean_dec_ref(v___y_4883_);
                    lean_dec(v_checkState_x3f_4845_);
                    v_a_4964_ = lean_ctor_get(v___x_4888_, 0);
                    v_isSharedCheck_4971_ = (!lean_is_exclusive(v___x_4888_)) as u8;
                    if v_isSharedCheck_4971_ == 0 {
                        v___x_4966_ = v___x_4888_;
                        v_isShared_4967_ = v_isSharedCheck_4971_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_4964_);
                        lean_dec(v___x_4888_);
                        v___x_4966_ = lean_box(0);
                        v_isShared_4967_ = v_isSharedCheck_4971_;
                        state = 17;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_checkState_x3f_4845_) == 1 {
                    lean_del_object(v___x_4891_);
                    v_fst_4893_ = lean_ctor_get(v_a_4889_, 0);
                    v_snd_4894_ = lean_ctor_get(v_a_4889_, 1);
                    v_isSharedCheck_4946_ = (!lean_is_exclusive(v_a_4889_)) as u8;
                    if v_isSharedCheck_4946_ == 0 {
                        v___x_4896_ = v_a_4889_;
                        v_isShared_4897_ = v_isSharedCheck_4946_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_4894_);
                        lean_inc(v_fst_4893_);
                        lean_dec(v_a_4889_);
                        v___x_4896_ = lean_box(0);
                        v_isShared_4897_ = v_isSharedCheck_4946_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_4886_);
                    lean_dec_ref(v___y_4883_);
                    lean_dec(v_checkState_x3f_4845_);
                    v_fst_4947_ = lean_ctor_get(v_a_4889_, 0);
                    v_isSharedCheck_4961_ = (!lean_is_exclusive(v_a_4889_)) as u8;
                    if v_isSharedCheck_4961_ == 0 {
                        v_unused_4962_ = lean_ctor_get(v_a_4889_, 1);
                        lean_dec(v_unused_4962_);
                        v___x_4949_ = v_a_4889_;
                        v_isShared_4950_ = v_isSharedCheck_4961_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_fst_4947_);
                        lean_dec(v_a_4889_);
                        v___x_4949_ = lean_box(0);
                        v_isShared_4950_ = v_isSharedCheck_4961_;
                        state = 14;
                        continue;
                    }
                }
            }
            6 => {
                v_val_4898_ = lean_ctor_get(v_checkState_x3f_4845_, 0);
                lean_inc(v_val_4898_);
                lean_dec_ref_known(v_checkState_x3f_4845_, 1);
                v___x_4899_ = lean_box(0);
                lean_inc(v_snd_4894_);
                v___x_4900_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_4893_, v_snd_4894_, v_val_4898_, v___x_4899_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v___y_4886_, v___y_4884_);
                if lean_obj_tag(v___x_4900_) == 0 {
                    v_a_4901_ = lean_ctor_get(v___x_4900_, 0);
                    lean_inc(v_a_4901_);
                    lean_dec_ref_known(v___x_4900_, 1);
                    if lean_obj_tag(v_a_4901_) == 1 {
                        lean_del_object(v___x_4896_);
                        lean_dec(v_snd_4894_);
                        v_val_4902_ = lean_ctor_get(v_a_4901_, 0);
                        v_isSharedCheck_4928_ = (!lean_is_exclusive(v_a_4901_)) as u8;
                        if v_isSharedCheck_4928_ == 0 {
                            v___x_4904_ = v_a_4901_;
                            v_isShared_4905_ = v_isSharedCheck_4928_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_val_4902_);
                            lean_dec(v_a_4901_);
                            v___x_4904_ = lean_box(0);
                            v_isShared_4905_ = v_isSharedCheck_4928_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4901_);
                        lean_dec_ref(v___y_4886_);
                        lean_dec_ref(v___y_4883_);
                        v___x_4929_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
                        if v_isShared_4897_ == 0 {
                            lean_ctor_set_tag(v___x_4896_, 7);
                            lean_ctor_set(v___x_4896_, 0, v___x_4929_);
                            v___x_4931_ = v___x_4896_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_4937_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4929_);
                            lean_ctor_set(v_reuseFailAlloc_4937_, 1, v_snd_4894_);
                            v___x_4931_ = v_reuseFailAlloc_4937_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4896_);
                    lean_dec(v_snd_4894_);
                    lean_dec_ref(v___y_4886_);
                    lean_dec_ref(v___y_4883_);
                    v_a_4938_ = lean_ctor_get(v___x_4900_, 0);
                    v_isSharedCheck_4945_ = (!lean_is_exclusive(v___x_4900_)) as u8;
                    if v_isSharedCheck_4945_ == 0 {
                        v___x_4940_ = v___x_4900_;
                        v_isShared_4941_ = v_isSharedCheck_4945_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_4938_);
                        lean_dec(v___x_4900_);
                        v___x_4940_ = lean_box(0);
                        v_isShared_4941_ = v_isSharedCheck_4945_;
                        state = 12;
                        continue;
                    }
                }
            }
            7 => {
                if v_addSubgoalsMsg_4844_ == 0 {
                    lean_del_object(v___x_4904_);
                    lean_dec_ref(v___y_4886_);
                    lean_dec_ref(v___y_4883_);
                    v_fst_4906_ = lean_ctor_get(v_val_4902_, 0);
                    lean_inc(v_fst_4906_);
                    v_snd_4907_ = lean_ctor_get(v_val_4902_, 1);
                    lean_inc(v_snd_4907_);
                    lean_dec(v_val_4902_);
                    v___y_4868_ = v_snd_4907_;
                    v___y_4869_ = v_fst_4906_;
                    state = 2;
                    continue;
                } else {
                    if v___y_4885_ == 0 {
                        v_fst_4908_ = lean_ctor_get(v_val_4902_, 0);
                        lean_inc(v_fst_4908_);
                        v_snd_4909_ = lean_ctor_get(v_val_4902_, 1);
                        lean_inc(v_snd_4909_);
                        lean_dec(v_val_4902_);
                        v___x_4910_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4;
                        v_sz_4911_ = lean_array_size(v___y_4883_);
                        v___x_4912_ = 0usize;
                        v___x_4913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v___y_4883_, v_sz_4911_, v___x_4912_, v___x_4910_, v_a_4851_, v_a_4852_, v___y_4886_, v___y_4884_);
                        lean_dec_ref(v___y_4886_);
                        lean_dec_ref(v___y_4883_);
                        if lean_obj_tag(v___x_4913_) == 0 {
                            v_a_4914_ = lean_ctor_get(v___x_4913_, 0);
                            lean_inc(v_a_4914_);
                            lean_dec_ref_known(v___x_4913_, 1);
                            if v_isShared_4905_ == 0 {
                                lean_ctor_set(v___x_4904_, 0, v_a_4914_);
                                v___x_4916_ = v___x_4904_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_4917_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4914_);
                                v___x_4916_ = v_reuseFailAlloc_4917_;
                                state = 8;
                                continue;
                            }
                        } else {
                            lean_dec(v_snd_4909_);
                            lean_dec(v_fst_4908_);
                            lean_del_object(v___x_4904_);
                            v_a_4918_ = lean_ctor_get(v___x_4913_, 0);
                            v_isSharedCheck_4925_ = (!lean_is_exclusive(v___x_4913_)) as u8;
                            if v_isSharedCheck_4925_ == 0 {
                                v___x_4920_ = v___x_4913_;
                                v_isShared_4921_ = v_isSharedCheck_4925_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_4918_);
                                lean_dec(v___x_4913_);
                                v___x_4920_ = lean_box(0);
                                v_isShared_4921_ = v_isSharedCheck_4925_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4904_);
                        lean_dec_ref(v___y_4886_);
                        lean_dec_ref(v___y_4883_);
                        v_fst_4926_ = lean_ctor_get(v_val_4902_, 0);
                        lean_inc(v_fst_4926_);
                        v_snd_4927_ = lean_ctor_get(v_val_4902_, 1);
                        lean_inc(v_snd_4927_);
                        lean_dec(v_val_4902_);
                        v___y_4868_ = v_snd_4927_;
                        v___y_4869_ = v_fst_4926_;
                        state = 2;
                        continue;
                    }
                }
            }
            8 => {
                v___y_4857_ = v_snd_4909_;
                v___y_4858_ = v_fst_4908_;
                v_postInfo_x3f_4859_ = v___x_4916_;
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_4921_ == 0 {
                    v___x_4923_ = v___x_4920_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4918_);
                    v___x_4923_ = v_reuseFailAlloc_4924_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4923_;
            }
            11 => {
                v___x_4932_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
                v___x_4933_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4933_, 0, v___x_4931_);
                lean_ctor_set(v___x_4933_, 1, v___x_4932_);
                v___x_4934_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6);
                if v___y_4887_ == 0 {
                    v___x_4935_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0;
                    v___y_4872_ = v___x_4933_;
                    v___y_4873_ = v___x_4934_;
                    v___y_4874_ = v___x_4935_;
                    state = 3;
                    continue;
                } else {
                    v___x_4936_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__7;
                    v___y_4872_ = v___x_4933_;
                    v___y_4873_ = v___x_4934_;
                    v___y_4874_ = v___x_4936_;
                    state = 3;
                    continue;
                }
            }
            12 => {
                if v_isShared_4941_ == 0 {
                    v___x_4943_ = v___x_4940_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
                    v___x_4943_ = v_reuseFailAlloc_4944_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4943_;
            }
            14 => {
                v___x_4951_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1;
                if v_isShared_4950_ == 0 {
                    lean_ctor_set(v___x_4949_, 1, v_fst_4947_);
                    lean_ctor_set(v___x_4949_, 0, v___x_4951_);
                    v___x_4953_ = v___x_4949_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4951_);
                    lean_ctor_set(v_reuseFailAlloc_4960_, 1, v_fst_4947_);
                    v___x_4953_ = v_reuseFailAlloc_4960_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4954_ = lean_box(0);
                v___x_4955_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_4955_, 0, v___x_4953_);
                lean_ctor_set(v___x_4955_, 1, v___x_4954_);
                lean_ctor_set(v___x_4955_, 2, v___x_4954_);
                lean_ctor_set(v___x_4955_, 3, v___x_4954_);
                lean_ctor_set(v___x_4955_, 4, v___x_4954_);
                lean_ctor_set(v___x_4955_, 5, v___x_4954_);
                v___x_4956_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4956_, 0, v___x_4955_);
                if v_isShared_4892_ == 0 {
                    lean_ctor_set(v___x_4891_, 0, v___x_4956_);
                    v___x_4958_ = v___x_4891_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4959_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4959_, 0, v___x_4956_);
                    v___x_4958_ = v_reuseFailAlloc_4959_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4958_;
            }
            17 => {
                if v_isShared_4967_ == 0 {
                    v___x_4969_ = v___x_4966_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4970_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4964_);
                    v___x_4969_ = v_reuseFailAlloc_4970_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4969_;
            }
            19 => {
                v___x_5008_ = l_Lean_maxRecDepth;
                v___x_5009_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(v___x_4990_, v___x_5008_);
                lean_inc_ref(v_inheritedTraceOptions_5006_);
                lean_inc(v_cancelTk_x3f_5004_);
                lean_inc(v_currMacroScope_5003_);
                lean_inc(v_quotContext_5002_);
                lean_inc(v_maxHeartbeats_5001_);
                lean_inc(v_initHeartbeats_5000_);
                lean_inc(v_openDecls_4999_);
                lean_inc(v_currNamespace_4998_);
                lean_inc(v_ref_4997_);
                lean_inc(v_currRecDepth_4996_);
                lean_inc_ref(v_fileMap_4995_);
                lean_inc_ref(v_fileName_4994_);
                v___x_5010_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_5010_, 0, v_fileName_4994_);
                lean_ctor_set(v___x_5010_, 1, v_fileMap_4995_);
                lean_ctor_set(v___x_5010_, 2, v___x_4990_);
                lean_ctor_set(v___x_5010_, 3, v_currRecDepth_4996_);
                lean_ctor_set(v___x_5010_, 4, v___x_5009_);
                lean_ctor_set(v___x_5010_, 5, v_ref_4997_);
                lean_ctor_set(v___x_5010_, 6, v_currNamespace_4998_);
                lean_ctor_set(v___x_5010_, 7, v_openDecls_4999_);
                lean_ctor_set(v___x_5010_, 8, v_initHeartbeats_5000_);
                lean_ctor_set(v___x_5010_, 9, v_maxHeartbeats_5001_);
                lean_ctor_set(v___x_5010_, 10, v_quotContext_5002_);
                lean_ctor_set(v___x_5010_, 11, v_currMacroScope_5003_);
                lean_ctor_set(v___x_5010_, 12, v_cancelTk_x3f_5004_);
                lean_ctor_set(v___x_5010_, 13, v_inheritedTraceOptions_5006_);
                lean_ctor_set_uint8(
                    v___x_5010_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_4992_,
                );
                lean_ctor_set_uint8(
                    v___x_5010_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5005_,
                );
                lean_inc_ref(v_e_4846_);
                v___x_5011_ =
                    l_Lean_Meta_getMVars(v_e_4846_, v_a_4851_, v_a_4852_, v___x_5010_, v___y_5007_);
                if lean_obj_tag(v___x_5011_) == 0 {
                    v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
                    lean_inc(v_a_5012_);
                    lean_dec_ref_known(v___x_5011_, 1);
                    v___x_5013_ = lean_array_get_size(v_a_5012_);
                    v___x_5014_ = lean_unsigned_to_nat(0);
                    v___x_5015_ = lean_nat_dec_eq(v___x_5013_, v___x_5014_);
                    if v___x_5015_ == 0 {
                        v___x_5016_ = 1;
                        v___y_4883_ = v_a_5012_;
                        v___y_4884_ = v___y_5007_;
                        v___y_4885_ = v___x_5015_;
                        v___y_4886_ = v___x_5010_;
                        v___y_4887_ = v___x_5016_;
                        state = 4;
                        continue;
                    } else {
                        v___y_4883_ = v_a_5012_;
                        v___y_4884_ = v___y_5007_;
                        v___y_4885_ = v___x_5015_;
                        v___y_4886_ = v___x_5010_;
                        v___y_4887_ = v___x_4989_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_5010_, 14);
                    lean_dec_ref(v_e_4846_);
                    lean_dec(v_checkState_x3f_4845_);
                    v_a_5017_ = lean_ctor_get(v___x_5011_, 0);
                    v_isSharedCheck_5024_ = (!lean_is_exclusive(v___x_5011_)) as u8;
                    if v_isSharedCheck_5024_ == 0 {
                        v___x_5019_ = v___x_5011_;
                        v_isShared_5020_ = v_isSharedCheck_5024_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_5017_);
                        lean_dec(v___x_5011_);
                        v___x_5019_ = lean_box(0);
                        v_isShared_5020_ = v_isSharedCheck_5024_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_5020_ == 0 {
                    v___x_5022_ = v___x_5019_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5017_);
                    v___x_5022_ = v_reuseFailAlloc_5023_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5022_;
            }
            22 => {
                if v___y_5026_ == 0 {
                    v___x_5027_ = lean_st_ref_take(v_a_4854_);
                    v_env_5028_ = lean_ctor_get(v___x_5027_, 0);
                    v_nextMacroScope_5029_ = lean_ctor_get(v___x_5027_, 1);
                    v_ngen_5030_ = lean_ctor_get(v___x_5027_, 2);
                    v_auxDeclNGen_5031_ = lean_ctor_get(v___x_5027_, 3);
                    v_traceState_5032_ = lean_ctor_get(v___x_5027_, 4);
                    v_messages_5033_ = lean_ctor_get(v___x_5027_, 6);
                    v_infoState_5034_ = lean_ctor_get(v___x_5027_, 7);
                    v_snapshotTasks_5035_ = lean_ctor_get(v___x_5027_, 8);
                    v_isSharedCheck_5045_ = (!lean_is_exclusive(v___x_5027_)) as u8;
                    if v_isSharedCheck_5045_ == 0 {
                        v_unused_5046_ = lean_ctor_get(v___x_5027_, 5);
                        lean_dec(v_unused_5046_);
                        v___x_5037_ = v___x_5027_;
                        v_isShared_5038_ = v_isSharedCheck_5045_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_5035_);
                        lean_inc(v_infoState_5034_);
                        lean_inc(v_messages_5033_);
                        lean_inc(v_traceState_5032_);
                        lean_inc(v_auxDeclNGen_5031_);
                        lean_inc(v_ngen_5030_);
                        lean_inc(v_nextMacroScope_5029_);
                        lean_inc(v_env_5028_);
                        lean_dec(v___x_5027_);
                        v___x_5037_ = lean_box(0);
                        v_isShared_5038_ = v_isSharedCheck_5045_;
                        state = 23;
                        continue;
                    }
                } else {
                    v_fileName_4994_ = v_fileName_4973_;
                    v_fileMap_4995_ = v_fileMap_4974_;
                    v_currRecDepth_4996_ = v_currRecDepth_4976_;
                    v_ref_4997_ = v_ref_4977_;
                    v_currNamespace_4998_ = v_currNamespace_4978_;
                    v_openDecls_4999_ = v_openDecls_4979_;
                    v_initHeartbeats_5000_ = v_initHeartbeats_4980_;
                    v_maxHeartbeats_5001_ = v_maxHeartbeats_4981_;
                    v_quotContext_5002_ = v_quotContext_4982_;
                    v_currMacroScope_5003_ = v_currMacroScope_4983_;
                    v_cancelTk_x3f_5004_ = v_cancelTk_x3f_4984_;
                    v_suppressElabErrors_5005_ = v_suppressElabErrors_4985_;
                    v_inheritedTraceOptions_5006_ = v_inheritedTraceOptions_4986_;
                    v___y_5007_ = v_a_4854_;
                    state = 19;
                    continue;
                }
            }
            23 => {
                v___x_5039_ = l_Lean_Kernel_enableDiag(v_env_5028_, v___x_4992_);
                v___x_5040_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2,
                );
                if v_isShared_5038_ == 0 {
                    lean_ctor_set(v___x_5037_, 5, v___x_5040_);
                    lean_ctor_set(v___x_5037_, 0, v___x_5039_);
                    v___x_5042_ = v___x_5037_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 0, v___x_5039_);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 1, v_nextMacroScope_5029_);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 2, v_ngen_5030_);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 3, v_auxDeclNGen_5031_);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 4, v_traceState_5032_);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 5, v___x_5040_);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 6, v_messages_5033_);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 7, v_infoState_5034_);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 8, v_snapshotTasks_5035_);
                    v___x_5042_ = v_reuseFailAlloc_5044_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_5043_ = lean_st_ref_set(v_a_4854_, v___x_5042_);
                v_fileName_4994_ = v_fileName_4973_;
                v_fileMap_4995_ = v_fileMap_4974_;
                v_currRecDepth_4996_ = v_currRecDepth_4976_;
                v_ref_4997_ = v_ref_4977_;
                v_currNamespace_4998_ = v_currNamespace_4978_;
                v_openDecls_4999_ = v_openDecls_4979_;
                v_initHeartbeats_5000_ = v_initHeartbeats_4980_;
                v_maxHeartbeats_5001_ = v_maxHeartbeats_4981_;
                v_quotContext_5002_ = v_quotContext_4982_;
                v_currMacroScope_5003_ = v_currMacroScope_4983_;
                v_cancelTk_x3f_5004_ = v_cancelTk_x3f_4984_;
                v_suppressElabErrors_5005_ = v_suppressElabErrors_4985_;
                v_inheritedTraceOptions_5006_ = v_inheritedTraceOptions_4986_;
                v___y_5007_ = v_a_4854_;
                state = 19;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___boxed(
    mut v_addSubgoalsMsg_5048_: *mut LeanObject,
    mut v_checkState_x3f_5049_: *mut LeanObject,
    mut v_e_5050_: *mut LeanObject,
    mut v_a_5051_: *mut LeanObject,
    mut v_a_5052_: *mut LeanObject,
    mut v_a_5053_: *mut LeanObject,
    mut v_a_5054_: *mut LeanObject,
    mut v_a_5055_: *mut LeanObject,
    mut v_a_5056_: *mut LeanObject,
    mut v_a_5057_: *mut LeanObject,
    mut v_a_5058_: *mut LeanObject,
    mut v_a_5059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_addSubgoalsMsg_boxed_5060_: u8 = 0;
    let mut v_res_5061_: *mut LeanObject = core::ptr::null_mut();
    v_addSubgoalsMsg_boxed_5060_ = (lean_unbox(v_addSubgoalsMsg_5048_) as u8);
    v_res_5061_ =
        l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(
            v_addSubgoalsMsg_boxed_5060_,
            v_checkState_x3f_5049_,
            v_e_5050_,
            v_a_5051_,
            v_a_5052_,
            v_a_5053_,
            v_a_5054_,
            v_a_5055_,
            v_a_5056_,
            v_a_5057_,
            v_a_5058_,
        );
    lean_dec(v_a_5058_);
    lean_dec_ref(v_a_5057_);
    lean_dec(v_a_5056_);
    lean_dec_ref(v_a_5055_);
    lean_dec(v_a_5054_);
    lean_dec_ref(v_a_5053_);
    lean_dec(v_a_5052_);
    lean_dec_ref(v_a_5051_);
    return v_res_5061_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(
    mut v_as_5062_: *mut LeanObject,
    mut v_sz_5063_: usize,
    mut v_i_5064_: usize,
    mut v_b_5065_: *mut LeanObject,
    mut v___y_5066_: *mut LeanObject,
    mut v___y_5067_: *mut LeanObject,
    mut v___y_5068_: *mut LeanObject,
    mut v___y_5069_: *mut LeanObject,
    mut v___y_5070_: *mut LeanObject,
    mut v___y_5071_: *mut LeanObject,
    mut v___y_5072_: *mut LeanObject,
    mut v___y_5073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    v___x_5075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_5062_, v_sz_5063_, v_i_5064_, v_b_5065_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_);
    return v___x_5075_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___boxed(
    mut v_as_5076_: *mut LeanObject,
    mut v_sz_5077_: *mut LeanObject,
    mut v_i_5078_: *mut LeanObject,
    mut v_b_5079_: *mut LeanObject,
    mut v___y_5080_: *mut LeanObject,
    mut v___y_5081_: *mut LeanObject,
    mut v___y_5082_: *mut LeanObject,
    mut v___y_5083_: *mut LeanObject,
    mut v___y_5084_: *mut LeanObject,
    mut v___y_5085_: *mut LeanObject,
    mut v___y_5086_: *mut LeanObject,
    mut v___y_5087_: *mut LeanObject,
    mut v___y_5088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5089_: usize = 0;
    let mut v_i_boxed_5090_: usize = 0;
    let mut v_res_5091_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5089_ = lean_unbox_usize(v_sz_5077_);
    lean_dec(v_sz_5077_);
    v_i_boxed_5090_ = lean_unbox_usize(v_i_5078_);
    lean_dec(v_i_5078_);
    v_res_5091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(v_as_5076_, v_sz_boxed_5089_, v_i_boxed_5090_, v_b_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
    lean_dec(v___y_5087_);
    lean_dec_ref(v___y_5086_);
    lean_dec(v___y_5085_);
    lean_dec_ref(v___y_5084_);
    lean_dec(v___y_5083_);
    lean_dec_ref(v___y_5082_);
    lean_dec(v___y_5081_);
    lean_dec_ref(v___y_5080_);
    lean_dec_ref(v_as_5076_);
    return v_res_5091_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(
    mut v_ref_5092_: *mut LeanObject,
    mut v_msgData_5093_: *mut LeanObject,
    mut v_severity_5094_: u8,
    mut v_isSilent_5095_: u8,
    mut v___y_5096_: *mut LeanObject,
    mut v___y_5097_: *mut LeanObject,
    mut v___y_5098_: *mut LeanObject,
    mut v___y_5099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5106_: u8 = 0;
    let mut v___y_5107_: u8 = 0;
    let mut v___y_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5125_: u8 = 0;
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5136_: u8 = 0;
    let mut v___y_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5140_: u8 = 0;
    let mut v___y_5141_: u8 = 0;
    let mut v___y_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5143_: u8 = 0;
    let mut v___y_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5151_: u8 = 0;
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: u8 = 0;
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5161_: u8 = 0;
    let mut v___y_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5166_: u8 = 0;
    let mut v___y_5167_: u8 = 0;
    let mut v___y_5168_: u8 = 0;
    let mut v___y_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5177_: u8 = 0;
    let mut v___y_5178_: u8 = 0;
    let mut v___y_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5180_: u8 = 0;
    let mut v_ref_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: u8 = 0;
    let mut v___y_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5190_: u8 = 0;
    let mut v___y_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5192_: u8 = 0;
    let mut v___y_5193_: u8 = 0;
    let mut v___y_5195_: u8 = 0;
    let mut v_fileName_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5200_: u8 = 0;
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: u8 = 0;
    let mut v___x_5205_: u8 = 0;
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: u8 = 0;
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: u8 = 0;
    let mut v___x_5211_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5185_ = 2;
                v___x_5210_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5094_, v___x_5185_);
                if v___x_5210_ == 0 {
                    v___y_5195_ = v___x_5210_;
                    state = 10;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_5093_);
                    v___x_5211_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5093_);
                    v___y_5195_ = v___x_5211_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_5111_ = lean_st_ref_take(v___y_5110_);
                v_currNamespace_5112_ = lean_ctor_get(v___y_5109_, 6);
                v_openDecls_5113_ = lean_ctor_get(v___y_5109_, 7);
                v_env_5114_ = lean_ctor_get(v___x_5111_, 0);
                v_nextMacroScope_5115_ = lean_ctor_get(v___x_5111_, 1);
                v_ngen_5116_ = lean_ctor_get(v___x_5111_, 2);
                v_auxDeclNGen_5117_ = lean_ctor_get(v___x_5111_, 3);
                v_traceState_5118_ = lean_ctor_get(v___x_5111_, 4);
                v_cache_5119_ = lean_ctor_get(v___x_5111_, 5);
                v_messages_5120_ = lean_ctor_get(v___x_5111_, 6);
                v_infoState_5121_ = lean_ctor_get(v___x_5111_, 7);
                v_snapshotTasks_5122_ = lean_ctor_get(v___x_5111_, 8);
                v_isSharedCheck_5136_ = (!lean_is_exclusive(v___x_5111_)) as u8;
                if v_isSharedCheck_5136_ == 0 {
                    v___x_5124_ = v___x_5111_;
                    v_isShared_5125_ = v_isSharedCheck_5136_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5122_);
                    lean_inc(v_infoState_5121_);
                    lean_inc(v_messages_5120_);
                    lean_inc(v_cache_5119_);
                    lean_inc(v_traceState_5118_);
                    lean_inc(v_auxDeclNGen_5117_);
                    lean_inc(v_ngen_5116_);
                    lean_inc(v_nextMacroScope_5115_);
                    lean_inc(v_env_5114_);
                    lean_dec(v___x_5111_);
                    v___x_5124_ = lean_box(0);
                    v_isShared_5125_ = v_isSharedCheck_5136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_5113_);
                lean_inc(v_currNamespace_5112_);
                v___x_5126_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5126_, 0, v_currNamespace_5112_);
                lean_ctor_set(v___x_5126_, 1, v_openDecls_5113_);
                v___x_5127_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5127_, 0, v___x_5126_);
                lean_ctor_set(v___x_5127_, 1, v___y_5104_);
                lean_inc_ref(v___y_5105_);
                lean_inc_ref(v___y_5102_);
                v___x_5128_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_5128_, 0, v___y_5102_);
                lean_ctor_set(v___x_5128_, 1, v___y_5108_);
                lean_ctor_set(v___x_5128_, 2, v___y_5103_);
                lean_ctor_set(v___x_5128_, 3, v___y_5105_);
                lean_ctor_set(v___x_5128_, 4, v___x_5127_);
                lean_ctor_set_uint8(
                    v___x_5128_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_5106_,
                );
                lean_ctor_set_uint8(
                    v___x_5128_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_5107_,
                );
                lean_ctor_set_uint8(
                    v___x_5128_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_5095_,
                );
                v___x_5129_ = l_Lean_MessageLog_add(v___x_5128_, v_messages_5120_);
                if v_isShared_5125_ == 0 {
                    lean_ctor_set(v___x_5124_, 6, v___x_5129_);
                    v___x_5131_ = v___x_5124_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5135_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_env_5114_);
                    lean_ctor_set(v_reuseFailAlloc_5135_, 1, v_nextMacroScope_5115_);
                    lean_ctor_set(v_reuseFailAlloc_5135_, 2, v_ngen_5116_);
                    lean_ctor_set(v_reuseFailAlloc_5135_, 3, v_auxDeclNGen_5117_);
                    lean_ctor_set(v_reuseFailAlloc_5135_, 4, v_traceState_5118_);
                    lean_ctor_set(v_reuseFailAlloc_5135_, 5, v_cache_5119_);
                    lean_ctor_set(v_reuseFailAlloc_5135_, 6, v___x_5129_);
                    lean_ctor_set(v_reuseFailAlloc_5135_, 7, v_infoState_5121_);
                    lean_ctor_set(v_reuseFailAlloc_5135_, 8, v_snapshotTasks_5122_);
                    v___x_5131_ = v_reuseFailAlloc_5135_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5132_ = lean_st_ref_set(v___y_5110_, v___x_5131_);
                v___x_5133_ = lean_box(0);
                v___x_5134_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5134_, 0, v___x_5133_);
                return v___x_5134_;
            }
            4 => {
                v___x_5146_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_5093_,
                    );
                v___x_5147_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_5146_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_);
                v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
                v_isSharedCheck_5161_ = (!lean_is_exclusive(v___x_5147_)) as u8;
                if v_isSharedCheck_5161_ == 0 {
                    v___x_5150_ = v___x_5147_;
                    v_isShared_5151_ = v_isSharedCheck_5161_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_5148_);
                    lean_dec(v___x_5147_);
                    v___x_5150_ = lean_box(0);
                    v_isShared_5151_ = v_isSharedCheck_5161_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_5144_, 2);
                v___x_5152_ = l_Lean_FileMap_toPosition(v___y_5144_, v___y_5142_);
                lean_dec(v___y_5142_);
                v___x_5153_ = l_Lean_FileMap_toPosition(v___y_5144_, v___y_5145_);
                lean_dec(v___y_5145_);
                v___x_5154_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5154_, 0, v___x_5153_);
                v___x_5155_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0;
                if v___y_5140_ == 0 {
                    lean_del_object(v___x_5150_);
                    lean_dec_ref(v___y_5138_);
                    v___y_5102_ = v___y_5139_;
                    v___y_5103_ = v___x_5154_;
                    v___y_5104_ = v_a_5148_;
                    v___y_5105_ = v___x_5155_;
                    v___y_5106_ = v___y_5141_;
                    v___y_5107_ = v___y_5143_;
                    v___y_5108_ = v___x_5152_;
                    v___y_5109_ = v___y_5098_;
                    v___y_5110_ = v___y_5099_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5148_);
                    v___x_5156_ = l_Lean_MessageData_hasTag(v___y_5138_, v_a_5148_);
                    if v___x_5156_ == 0 {
                        lean_dec_ref_known(v___x_5154_, 1);
                        lean_dec_ref(v___x_5152_);
                        lean_dec(v_a_5148_);
                        v___x_5157_ = lean_box(0);
                        if v_isShared_5151_ == 0 {
                            lean_ctor_set(v___x_5150_, 0, v___x_5157_);
                            v___x_5159_ = v___x_5150_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5160_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5160_, 0, v___x_5157_);
                            v___x_5159_ = v_reuseFailAlloc_5160_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5150_);
                        v___y_5102_ = v___y_5139_;
                        v___y_5103_ = v___x_5154_;
                        v___y_5104_ = v_a_5148_;
                        v___y_5105_ = v___x_5155_;
                        v___y_5106_ = v___y_5141_;
                        v___y_5107_ = v___y_5143_;
                        v___y_5108_ = v___x_5152_;
                        v___y_5109_ = v___y_5098_;
                        v___y_5110_ = v___y_5099_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_5159_;
            }
            7 => {
                v___x_5171_ = l_Lean_Syntax_getTailPos_x3f(v___y_5164_, v___y_5167_);
                lean_dec(v___y_5164_);
                if lean_obj_tag(v___x_5171_) == 0 {
                    lean_inc(v___y_5170_);
                    v___y_5138_ = v___y_5163_;
                    v___y_5139_ = v___y_5165_;
                    v___y_5140_ = v___y_5166_;
                    v___y_5141_ = v___y_5167_;
                    v___y_5142_ = v___y_5170_;
                    v___y_5143_ = v___y_5168_;
                    v___y_5144_ = v___y_5169_;
                    v___y_5145_ = v___y_5170_;
                    state = 4;
                    continue;
                } else {
                    v_val_5172_ = lean_ctor_get(v___x_5171_, 0);
                    lean_inc(v_val_5172_);
                    lean_dec_ref_known(v___x_5171_, 1);
                    v___y_5138_ = v___y_5163_;
                    v___y_5139_ = v___y_5165_;
                    v___y_5140_ = v___y_5166_;
                    v___y_5141_ = v___y_5167_;
                    v___y_5142_ = v___y_5170_;
                    v___y_5143_ = v___y_5168_;
                    v___y_5144_ = v___y_5169_;
                    v___y_5145_ = v_val_5172_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_5181_ = l_Lean_replaceRef(v_ref_5092_, v___y_5176_);
                v___x_5182_ = l_Lean_Syntax_getPos_x3f(v_ref_5181_, v___y_5178_);
                if lean_obj_tag(v___x_5182_) == 0 {
                    v___x_5183_ = lean_unsigned_to_nat(0);
                    v___y_5163_ = v___y_5174_;
                    v___y_5164_ = v_ref_5181_;
                    v___y_5165_ = v___y_5175_;
                    v___y_5166_ = v___y_5177_;
                    v___y_5167_ = v___y_5178_;
                    v___y_5168_ = v___y_5180_;
                    v___y_5169_ = v___y_5179_;
                    v___y_5170_ = v___x_5183_;
                    state = 7;
                    continue;
                } else {
                    v_val_5184_ = lean_ctor_get(v___x_5182_, 0);
                    lean_inc(v_val_5184_);
                    lean_dec_ref_known(v___x_5182_, 1);
                    v___y_5163_ = v___y_5174_;
                    v___y_5164_ = v_ref_5181_;
                    v___y_5165_ = v___y_5175_;
                    v___y_5166_ = v___y_5177_;
                    v___y_5167_ = v___y_5178_;
                    v___y_5168_ = v___y_5180_;
                    v___y_5169_ = v___y_5179_;
                    v___y_5170_ = v_val_5184_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_5193_ == 0 {
                    v___y_5174_ = v___y_5189_;
                    v___y_5175_ = v___y_5188_;
                    v___y_5176_ = v___y_5187_;
                    v___y_5177_ = v___y_5190_;
                    v___y_5178_ = v___y_5192_;
                    v___y_5179_ = v___y_5191_;
                    v___y_5180_ = v_severity_5094_;
                    state = 8;
                    continue;
                } else {
                    v___y_5174_ = v___y_5189_;
                    v___y_5175_ = v___y_5188_;
                    v___y_5176_ = v___y_5187_;
                    v___y_5177_ = v___y_5190_;
                    v___y_5178_ = v___y_5192_;
                    v___y_5179_ = v___y_5191_;
                    v___y_5180_ = v___x_5185_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_5195_ == 0 {
                    v_fileName_5196_ = lean_ctor_get(v___y_5098_, 0);
                    v_fileMap_5197_ = lean_ctor_get(v___y_5098_, 1);
                    v_options_5198_ = lean_ctor_get(v___y_5098_, 2);
                    v_ref_5199_ = lean_ctor_get(v___y_5098_, 5);
                    v_suppressElabErrors_5200_ = lean_ctor_get_uint8(
                        v___y_5098_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_5201_ = lean_box((v___y_5195_) as usize);
                    v___x_5202_ = lean_box((v_suppressElabErrors_5200_) as usize);
                    v___f_5203_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_5203_, 0, v___x_5201_);
                    lean_closure_set(v___f_5203_, 1, v___x_5202_);
                    v___x_5204_ = 1;
                    v___x_5205_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5094_, v___x_5204_);
                    if v___x_5205_ == 0 {
                        v___y_5187_ = v_ref_5199_;
                        v___y_5188_ = v_fileName_5196_;
                        v___y_5189_ = v___f_5203_;
                        v___y_5190_ = v_suppressElabErrors_5200_;
                        v___y_5191_ = v_fileMap_5197_;
                        v___y_5192_ = v___y_5195_;
                        v___y_5193_ = v___x_5205_;
                        state = 9;
                        continue;
                    } else {
                        v___x_5206_ = l_Lean_warningAsError;
                        v___x_5207_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_5198_, v___x_5206_);
                        v___y_5187_ = v_ref_5199_;
                        v___y_5188_ = v_fileName_5196_;
                        v___y_5189_ = v___f_5203_;
                        v___y_5190_ = v_suppressElabErrors_5200_;
                        v___y_5191_ = v_fileMap_5197_;
                        v___y_5192_ = v___y_5195_;
                        v___y_5193_ = v___x_5207_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_5093_);
                    v___x_5208_ = lean_box(0);
                    v___x_5209_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5209_, 0, v___x_5208_);
                    return v___x_5209_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_5212_: *mut LeanObject,
    mut v_msgData_5213_: *mut LeanObject,
    mut v_severity_5214_: *mut LeanObject,
    mut v_isSilent_5215_: *mut LeanObject,
    mut v___y_5216_: *mut LeanObject,
    mut v___y_5217_: *mut LeanObject,
    mut v___y_5218_: *mut LeanObject,
    mut v___y_5219_: *mut LeanObject,
    mut v___y_5220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5221_: u8 = 0;
    let mut v_isSilent_boxed_5222_: u8 = 0;
    let mut v_res_5223_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5221_ = (lean_unbox(v_severity_5214_) as u8);
    v_isSilent_boxed_5222_ = (lean_unbox(v_isSilent_5215_) as u8);
    v_res_5223_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_5212_, v_msgData_5213_, v_severity_boxed_5221_, v_isSilent_boxed_5222_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_);
    lean_dec(v___y_5219_);
    lean_dec_ref(v___y_5218_);
    lean_dec(v___y_5217_);
    lean_dec_ref(v___y_5216_);
    lean_dec(v_ref_5212_);
    return v_res_5223_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(
    mut v_msgData_5224_: *mut LeanObject,
    mut v_severity_5225_: u8,
    mut v_isSilent_5226_: u8,
    mut v___y_5227_: *mut LeanObject,
    mut v___y_5228_: *mut LeanObject,
    mut v___y_5229_: *mut LeanObject,
    mut v___y_5230_: *mut LeanObject,
    mut v___y_5231_: *mut LeanObject,
    mut v___y_5232_: *mut LeanObject,
    mut v___y_5233_: *mut LeanObject,
    mut v___y_5234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5236_ = lean_ctor_get(v___y_5233_, 5);
    v___x_5237_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_5236_, v_msgData_5224_, v_severity_5225_, v_isSilent_5226_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_);
    return v___x_5237_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0___boxed(
    mut v_msgData_5238_: *mut LeanObject,
    mut v_severity_5239_: *mut LeanObject,
    mut v_isSilent_5240_: *mut LeanObject,
    mut v___y_5241_: *mut LeanObject,
    mut v___y_5242_: *mut LeanObject,
    mut v___y_5243_: *mut LeanObject,
    mut v___y_5244_: *mut LeanObject,
    mut v___y_5245_: *mut LeanObject,
    mut v___y_5246_: *mut LeanObject,
    mut v___y_5247_: *mut LeanObject,
    mut v___y_5248_: *mut LeanObject,
    mut v___y_5249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5250_: u8 = 0;
    let mut v_isSilent_boxed_5251_: u8 = 0;
    let mut v_res_5252_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5250_ = (lean_unbox(v_severity_5239_) as u8);
    v_isSilent_boxed_5251_ = (lean_unbox(v_isSilent_5240_) as u8);
    v_res_5252_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_5238_, v_severity_boxed_5250_, v_isSilent_boxed_5251_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
    lean_dec(v___y_5248_);
    lean_dec_ref(v___y_5247_);
    lean_dec(v___y_5246_);
    lean_dec_ref(v___y_5245_);
    lean_dec(v___y_5244_);
    lean_dec_ref(v___y_5243_);
    lean_dec(v___y_5242_);
    lean_dec_ref(v___y_5241_);
    return v_res_5252_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(
    mut v_msgData_5253_: *mut LeanObject,
    mut v___y_5254_: *mut LeanObject,
    mut v___y_5255_: *mut LeanObject,
    mut v___y_5256_: *mut LeanObject,
    mut v___y_5257_: *mut LeanObject,
    mut v___y_5258_: *mut LeanObject,
    mut v___y_5259_: *mut LeanObject,
    mut v___y_5260_: *mut LeanObject,
    mut v___y_5261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: u8 = 0;
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    v___x_5263_ = 0;
    v___x_5264_ = 0;
    v___x_5265_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_5253_, v___x_5263_, v___x_5264_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_);
    return v___x_5265_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0___boxed(
    mut v_msgData_5266_: *mut LeanObject,
    mut v___y_5267_: *mut LeanObject,
    mut v___y_5268_: *mut LeanObject,
    mut v___y_5269_: *mut LeanObject,
    mut v___y_5270_: *mut LeanObject,
    mut v___y_5271_: *mut LeanObject,
    mut v___y_5272_: *mut LeanObject,
    mut v___y_5273_: *mut LeanObject,
    mut v___y_5274_: *mut LeanObject,
    mut v___y_5275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5276_: *mut LeanObject = core::ptr::null_mut();
    v_res_5276_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(
        v_msgData_5266_,
        v___y_5267_,
        v___y_5268_,
        v___y_5269_,
        v___y_5270_,
        v___y_5271_,
        v___y_5272_,
        v___y_5273_,
        v___y_5274_,
    );
    lean_dec(v___y_5274_);
    lean_dec_ref(v___y_5273_);
    lean_dec(v___y_5272_);
    lean_dec_ref(v___y_5271_);
    lean_dec(v___y_5270_);
    lean_dec_ref(v___y_5269_);
    lean_dec(v___y_5268_);
    lean_dec_ref(v___y_5267_);
    return v_res_5276_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addExactSuggestion(
    mut v_ref_5278_: *mut LeanObject,
    mut v_e_5279_: *mut LeanObject,
    mut v_origSpan_x3f_5280_: *mut LeanObject,
    mut v_addSubgoalsMsg_5281_: u8,
    mut v_codeActionPrefix_x3f_5282_: *mut LeanObject,
    mut v_checkState_x3f_5283_: *mut LeanObject,
    mut v_tacticErrorAsInfo_5284_: u8,
    mut v_a_5285_: *mut LeanObject,
    mut v_a_5286_: *mut LeanObject,
    mut v_a_5287_: *mut LeanObject,
    mut v_a_5288_: *mut LeanObject,
    mut v_a_5289_: *mut LeanObject,
    mut v_a_5290_: *mut LeanObject,
    mut v_a_5291_: *mut LeanObject,
    mut v_a_5292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: u8 = 0;
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5308_: u8 = 0;
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5294_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_5281_, v_checkState_x3f_5283_, v_e_5279_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_);
                if lean_obj_tag(v___x_5294_) == 0 {
                    v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
                    lean_inc(v_a_5295_);
                    lean_dec_ref_known(v___x_5294_, 1);
                    if lean_obj_tag(v_a_5295_) == 0 {
                        v_val_5296_ = lean_ctor_get(v_a_5295_, 0);
                        lean_inc(v_val_5296_);
                        lean_dec_ref_known(v_a_5295_, 1);
                        v___x_5297_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0;
                        v___x_5298_ = 4;
                        v___x_5299_ = l_Lean_MessageData_nil;
                        v___x_5300_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                            v_ref_5278_,
                            v_val_5296_,
                            v_origSpan_x3f_5280_,
                            v___x_5297_,
                            v_codeActionPrefix_x3f_5282_,
                            v___x_5298_,
                            v___x_5299_,
                            v_a_5291_,
                            v_a_5292_,
                        );
                        return v___x_5300_;
                    } else {
                        lean_dec(v_codeActionPrefix_x3f_5282_);
                        lean_dec(v_origSpan_x3f_5280_);
                        lean_dec(v_ref_5278_);
                        if v_tacticErrorAsInfo_5284_ == 0 {
                            v_val_5301_ = lean_ctor_get(v_a_5295_, 0);
                            lean_inc(v_val_5301_);
                            lean_dec_ref_known(v_a_5295_, 1);
                            v___x_5302_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_val_5301_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_);
                            return v___x_5302_;
                        } else {
                            v_val_5303_ = lean_ctor_get(v_a_5295_, 0);
                            lean_inc(v_val_5303_);
                            lean_dec_ref_known(v_a_5295_, 1);
                            v___x_5304_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_val_5303_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_);
                            return v___x_5304_;
                        }
                    }
                } else {
                    lean_dec(v_codeActionPrefix_x3f_5282_);
                    lean_dec(v_origSpan_x3f_5280_);
                    lean_dec(v_ref_5278_);
                    v_a_5305_ = lean_ctor_get(v___x_5294_, 0);
                    v_isSharedCheck_5312_ = (!lean_is_exclusive(v___x_5294_)) as u8;
                    if v_isSharedCheck_5312_ == 0 {
                        v___x_5307_ = v___x_5294_;
                        v_isShared_5308_ = v_isSharedCheck_5312_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5305_);
                        lean_dec(v___x_5294_);
                        v___x_5307_ = lean_box(0);
                        v_isShared_5308_ = v_isSharedCheck_5312_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5308_ == 0 {
                    v___x_5310_ = v___x_5307_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
                    v___x_5310_ = v_reuseFailAlloc_5311_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addExactSuggestion___boxed(
    mut v_ref_5313_: *mut LeanObject,
    mut v_e_5314_: *mut LeanObject,
    mut v_origSpan_x3f_5315_: *mut LeanObject,
    mut v_addSubgoalsMsg_5316_: *mut LeanObject,
    mut v_codeActionPrefix_x3f_5317_: *mut LeanObject,
    mut v_checkState_x3f_5318_: *mut LeanObject,
    mut v_tacticErrorAsInfo_5319_: *mut LeanObject,
    mut v_a_5320_: *mut LeanObject,
    mut v_a_5321_: *mut LeanObject,
    mut v_a_5322_: *mut LeanObject,
    mut v_a_5323_: *mut LeanObject,
    mut v_a_5324_: *mut LeanObject,
    mut v_a_5325_: *mut LeanObject,
    mut v_a_5326_: *mut LeanObject,
    mut v_a_5327_: *mut LeanObject,
    mut v_a_5328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_addSubgoalsMsg_boxed_5329_: u8 = 0;
    let mut v_tacticErrorAsInfo_boxed_5330_: u8 = 0;
    let mut v_res_5331_: *mut LeanObject = core::ptr::null_mut();
    v_addSubgoalsMsg_boxed_5329_ = (lean_unbox(v_addSubgoalsMsg_5316_) as u8);
    v_tacticErrorAsInfo_boxed_5330_ = (lean_unbox(v_tacticErrorAsInfo_5319_) as u8);
    v_res_5331_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(
        v_ref_5313_,
        v_e_5314_,
        v_origSpan_x3f_5315_,
        v_addSubgoalsMsg_boxed_5329_,
        v_codeActionPrefix_x3f_5317_,
        v_checkState_x3f_5318_,
        v_tacticErrorAsInfo_boxed_5330_,
        v_a_5320_,
        v_a_5321_,
        v_a_5322_,
        v_a_5323_,
        v_a_5324_,
        v_a_5325_,
        v_a_5326_,
        v_a_5327_,
    );
    lean_dec(v_a_5327_);
    lean_dec_ref(v_a_5326_);
    lean_dec(v_a_5325_);
    lean_dec_ref(v_a_5324_);
    lean_dec(v_a_5323_);
    lean_dec_ref(v_a_5322_);
    lean_dec(v_a_5321_);
    lean_dec_ref(v_a_5320_);
    return v_res_5331_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(
    mut v_ref_5332_: *mut LeanObject,
    mut v_msgData_5333_: *mut LeanObject,
    mut v_severity_5334_: u8,
    mut v_isSilent_5335_: u8,
    mut v___y_5336_: *mut LeanObject,
    mut v___y_5337_: *mut LeanObject,
    mut v___y_5338_: *mut LeanObject,
    mut v___y_5339_: *mut LeanObject,
    mut v___y_5340_: *mut LeanObject,
    mut v___y_5341_: *mut LeanObject,
    mut v___y_5342_: *mut LeanObject,
    mut v___y_5343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    v___x_5345_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_5332_, v_msgData_5333_, v_severity_5334_, v_isSilent_5335_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_);
    return v___x_5345_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___boxed(
    mut v_ref_5346_: *mut LeanObject,
    mut v_msgData_5347_: *mut LeanObject,
    mut v_severity_5348_: *mut LeanObject,
    mut v_isSilent_5349_: *mut LeanObject,
    mut v___y_5350_: *mut LeanObject,
    mut v___y_5351_: *mut LeanObject,
    mut v___y_5352_: *mut LeanObject,
    mut v___y_5353_: *mut LeanObject,
    mut v___y_5354_: *mut LeanObject,
    mut v___y_5355_: *mut LeanObject,
    mut v___y_5356_: *mut LeanObject,
    mut v___y_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5359_: u8 = 0;
    let mut v_isSilent_boxed_5360_: u8 = 0;
    let mut v_res_5361_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5359_ = (lean_unbox(v_severity_5348_) as u8);
    v_isSilent_boxed_5360_ = (lean_unbox(v_isSilent_5349_) as u8);
    v_res_5361_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(v_ref_5346_, v_msgData_5347_, v_severity_boxed_5359_, v_isSilent_boxed_5360_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_);
    lean_dec(v___y_5357_);
    lean_dec_ref(v___y_5356_);
    lean_dec(v___y_5355_);
    lean_dec_ref(v___y_5354_);
    lean_dec(v___y_5353_);
    lean_dec_ref(v___y_5352_);
    lean_dec(v___y_5351_);
    lean_dec_ref(v___y_5350_);
    lean_dec(v_ref_5346_);
    return v_res_5361_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(
    mut v_tacticErrorAsInfo_5362_: u8,
    mut v_as_5363_: *mut LeanObject,
    mut v_sz_5364_: usize,
    mut v_i_5365_: usize,
    mut v_b_5366_: *mut LeanObject,
    mut v___y_5367_: *mut LeanObject,
    mut v___y_5368_: *mut LeanObject,
    mut v___y_5369_: *mut LeanObject,
    mut v___y_5370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: usize = 0;
    let mut v___x_5375_: usize = 0;
    let mut v___x_5377_: u8 = 0;
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5383_: u8 = 0;
    let mut v_a_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5400_: u8 = 0;
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5404_: u8 = 0;
    let mut v_isSharedCheck_5405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5377_ = lean_usize_dec_lt(v_i_5365_, v_sz_5364_);
                if v___x_5377_ == 0 {
                    v___x_5378_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5378_, 0, v_b_5366_);
                    return v___x_5378_;
                } else {
                    v_fst_5379_ = lean_ctor_get(v_b_5366_, 0);
                    v_snd_5380_ = lean_ctor_get(v_b_5366_, 1);
                    v_isSharedCheck_5405_ = (!lean_is_exclusive(v_b_5366_)) as u8;
                    if v_isSharedCheck_5405_ == 0 {
                        v___x_5382_ = v_b_5366_;
                        v_isShared_5383_ = v_isSharedCheck_5405_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_5380_);
                        lean_inc(v_fst_5379_);
                        lean_dec(v_b_5366_);
                        v___x_5382_ = lean_box(0);
                        v_isShared_5383_ = v_isSharedCheck_5405_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5374_ = 1usize;
                v___x_5375_ = lean_usize_add(v_i_5365_, v___x_5374_);
                v_i_5365_ = v___x_5375_;
                v_b_5366_ = v_a_5373_;
                state = 0;
                continue;
            }
            2 => {
                v_a_5384_ = lean_array_uget_borrowed(v_as_5363_, v_i_5365_);
                if lean_obj_tag(v_a_5384_) == 0 {
                    v_val_5385_ = lean_ctor_get(v_a_5384_, 0);
                    lean_inc(v_val_5385_);
                    v___x_5386_ = lean_array_push(v_fst_5379_, v_val_5385_);
                    if v_isShared_5383_ == 0 {
                        lean_ctor_set(v___x_5382_, 0, v___x_5386_);
                        v___x_5388_ = v___x_5382_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5389_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5389_, 0, v___x_5386_);
                        lean_ctor_set(v_reuseFailAlloc_5389_, 1, v_snd_5380_);
                        v___x_5388_ = v_reuseFailAlloc_5389_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_5390_ = lean_ctor_get(v_a_5384_, 0);
                    if v_tacticErrorAsInfo_5362_ == 0 {
                        lean_inc(v_val_5390_);
                        v___x_5396_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_val_5390_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_);
                        if lean_obj_tag(v___x_5396_) == 0 {
                            lean_dec_ref_known(v___x_5396_, 1);
                            state = 4;
                            continue;
                        } else {
                            lean_del_object(v___x_5382_);
                            lean_dec(v_snd_5380_);
                            lean_dec(v_fst_5379_);
                            v_a_5397_ = lean_ctor_get(v___x_5396_, 0);
                            v_isSharedCheck_5404_ = (!lean_is_exclusive(v___x_5396_)) as u8;
                            if v_isSharedCheck_5404_ == 0 {
                                v___x_5399_ = v___x_5396_;
                                v_isShared_5400_ = v_isSharedCheck_5404_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_5397_);
                                lean_dec(v___x_5396_);
                                v___x_5399_ = lean_box(0);
                                v_isShared_5400_ = v_isSharedCheck_5404_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_5373_ = v___x_5388_;
                state = 1;
                continue;
            }
            4 => {
                lean_inc(v_val_5390_);
                v___x_5392_ = lean_array_push(v_snd_5380_, v_val_5390_);
                if v_isShared_5383_ == 0 {
                    lean_ctor_set(v___x_5382_, 1, v___x_5392_);
                    v___x_5394_ = v___x_5382_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5395_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_fst_5379_);
                    lean_ctor_set(v_reuseFailAlloc_5395_, 1, v___x_5392_);
                    v___x_5394_ = v_reuseFailAlloc_5395_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_5373_ = v___x_5394_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_5400_ == 0 {
                    v___x_5402_ = v___x_5399_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5403_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_a_5397_);
                    v___x_5402_ = v_reuseFailAlloc_5403_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg___boxed(
    mut v_tacticErrorAsInfo_5406_: *mut LeanObject,
    mut v_as_5407_: *mut LeanObject,
    mut v_sz_5408_: *mut LeanObject,
    mut v_i_5409_: *mut LeanObject,
    mut v_b_5410_: *mut LeanObject,
    mut v___y_5411_: *mut LeanObject,
    mut v___y_5412_: *mut LeanObject,
    mut v___y_5413_: *mut LeanObject,
    mut v___y_5414_: *mut LeanObject,
    mut v___y_5415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tacticErrorAsInfo_boxed_5416_: u8 = 0;
    let mut v_sz_boxed_5417_: usize = 0;
    let mut v_i_boxed_5418_: usize = 0;
    let mut v_res_5419_: *mut LeanObject = core::ptr::null_mut();
    v_tacticErrorAsInfo_boxed_5416_ = (lean_unbox(v_tacticErrorAsInfo_5406_) as u8);
    v_sz_boxed_5417_ = lean_unbox_usize(v_sz_5408_);
    lean_dec(v_sz_5408_);
    v_i_boxed_5418_ = lean_unbox_usize(v_i_5409_);
    lean_dec(v_i_5409_);
    v_res_5419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_boxed_5416_, v_as_5407_, v_sz_boxed_5417_, v_i_boxed_5418_, v_b_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_);
    lean_dec(v___y_5414_);
    lean_dec_ref(v___y_5413_);
    lean_dec(v___y_5412_);
    lean_dec_ref(v___y_5411_);
    lean_dec_ref(v_as_5407_);
    return v_res_5419_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(
    mut v_addSubgoalsMsg_5420_: u8,
    mut v_checkState_x3f_5421_: *mut LeanObject,
    mut v_sz_5422_: usize,
    mut v_i_5423_: usize,
    mut v_bs_5424_: *mut LeanObject,
    mut v___y_5425_: *mut LeanObject,
    mut v___y_5426_: *mut LeanObject,
    mut v___y_5427_: *mut LeanObject,
    mut v___y_5428_: *mut LeanObject,
    mut v___y_5429_: *mut LeanObject,
    mut v___y_5430_: *mut LeanObject,
    mut v___y_5431_: *mut LeanObject,
    mut v___y_5432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5434_: u8 = 0;
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: usize = 0;
    let mut v___x_5442_: usize = 0;
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5448_: u8 = 0;
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5434_ = lean_usize_dec_lt(v_i_5423_, v_sz_5422_);
                if v___x_5434_ == 0 {
                    lean_dec(v_checkState_x3f_5421_);
                    v___x_5435_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5435_, 0, v_bs_5424_);
                    return v___x_5435_;
                } else {
                    v_v_5436_ = lean_array_uget_borrowed(v_bs_5424_, v_i_5423_);
                    lean_inc(v_v_5436_);
                    lean_inc(v_checkState_x3f_5421_);
                    v___x_5437_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_5420_, v_checkState_x3f_5421_, v_v_5436_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_);
                    if lean_obj_tag(v___x_5437_) == 0 {
                        v_a_5438_ = lean_ctor_get(v___x_5437_, 0);
                        lean_inc(v_a_5438_);
                        lean_dec_ref_known(v___x_5437_, 1);
                        v___x_5439_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5440_ = lean_array_uset(v_bs_5424_, v_i_5423_, v___x_5439_);
                        v___x_5441_ = 1usize;
                        v___x_5442_ = lean_usize_add(v_i_5423_, v___x_5441_);
                        v___x_5443_ = lean_array_uset(v_bs_x27_5440_, v_i_5423_, v_a_5438_);
                        v_i_5423_ = v___x_5442_;
                        v_bs_5424_ = v___x_5443_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5424_);
                        lean_dec(v_checkState_x3f_5421_);
                        v_a_5445_ = lean_ctor_get(v___x_5437_, 0);
                        v_isSharedCheck_5452_ = (!lean_is_exclusive(v___x_5437_)) as u8;
                        if v_isSharedCheck_5452_ == 0 {
                            v___x_5447_ = v___x_5437_;
                            v_isShared_5448_ = v_isSharedCheck_5452_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5445_);
                            lean_dec(v___x_5437_);
                            v___x_5447_ = lean_box(0);
                            v_isShared_5448_ = v_isSharedCheck_5452_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5448_ == 0 {
                    v___x_5450_ = v___x_5447_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5451_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5451_, 0, v_a_5445_);
                    v___x_5450_ = v_reuseFailAlloc_5451_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5450_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0___boxed(
    mut v_addSubgoalsMsg_5453_: *mut LeanObject,
    mut v_checkState_x3f_5454_: *mut LeanObject,
    mut v_sz_5455_: *mut LeanObject,
    mut v_i_5456_: *mut LeanObject,
    mut v_bs_5457_: *mut LeanObject,
    mut v___y_5458_: *mut LeanObject,
    mut v___y_5459_: *mut LeanObject,
    mut v___y_5460_: *mut LeanObject,
    mut v___y_5461_: *mut LeanObject,
    mut v___y_5462_: *mut LeanObject,
    mut v___y_5463_: *mut LeanObject,
    mut v___y_5464_: *mut LeanObject,
    mut v___y_5465_: *mut LeanObject,
    mut v___y_5466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_addSubgoalsMsg_boxed_5467_: u8 = 0;
    let mut v_sz_boxed_5468_: usize = 0;
    let mut v_i_boxed_5469_: usize = 0;
    let mut v_res_5470_: *mut LeanObject = core::ptr::null_mut();
    v_addSubgoalsMsg_boxed_5467_ = (lean_unbox(v_addSubgoalsMsg_5453_) as u8);
    v_sz_boxed_5468_ = lean_unbox_usize(v_sz_5455_);
    lean_dec(v_sz_5455_);
    v_i_boxed_5469_ = lean_unbox_usize(v_i_5456_);
    lean_dec(v_i_5456_);
    v_res_5470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_boxed_5467_, v_checkState_x3f_5454_, v_sz_boxed_5468_, v_i_boxed_5469_, v_bs_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_);
    lean_dec(v___y_5465_);
    lean_dec_ref(v___y_5464_);
    lean_dec(v___y_5463_);
    lean_dec_ref(v___y_5462_);
    lean_dec(v___y_5461_);
    lean_dec_ref(v___y_5460_);
    lean_dec(v___y_5459_);
    lean_dec_ref(v___y_5458_);
    return v_res_5470_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(
    mut v_as_5471_: *mut LeanObject,
    mut v_sz_5472_: usize,
    mut v_i_5473_: usize,
    mut v_b_5474_: *mut LeanObject,
    mut v___y_5475_: *mut LeanObject,
    mut v___y_5476_: *mut LeanObject,
    mut v___y_5477_: *mut LeanObject,
    mut v___y_5478_: *mut LeanObject,
    mut v___y_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5484_: u8 = 0;
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: usize = 0;
    let mut v___x_5490_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5484_ = lean_usize_dec_lt(v_i_5473_, v_sz_5472_);
                if v___x_5484_ == 0 {
                    v___x_5485_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5485_, 0, v_b_5474_);
                    return v___x_5485_;
                } else {
                    v_a_5486_ = lean_array_uget_borrowed(v_as_5471_, v_i_5473_);
                    lean_inc(v_a_5486_);
                    v___x_5487_ =
                        l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(
                            v_a_5486_,
                            v___y_5475_,
                            v___y_5476_,
                            v___y_5477_,
                            v___y_5478_,
                            v___y_5479_,
                            v___y_5480_,
                            v___y_5481_,
                            v___y_5482_,
                        );
                    if lean_obj_tag(v___x_5487_) == 0 {
                        lean_dec_ref_known(v___x_5487_, 1);
                        v___x_5488_ = lean_box(0);
                        v___x_5489_ = 1usize;
                        v___x_5490_ = lean_usize_add(v_i_5473_, v___x_5489_);
                        v_i_5473_ = v___x_5490_;
                        v_b_5474_ = v___x_5488_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5487_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2___boxed(
    mut v_as_5492_: *mut LeanObject,
    mut v_sz_5493_: *mut LeanObject,
    mut v_i_5494_: *mut LeanObject,
    mut v_b_5495_: *mut LeanObject,
    mut v___y_5496_: *mut LeanObject,
    mut v___y_5497_: *mut LeanObject,
    mut v___y_5498_: *mut LeanObject,
    mut v___y_5499_: *mut LeanObject,
    mut v___y_5500_: *mut LeanObject,
    mut v___y_5501_: *mut LeanObject,
    mut v___y_5502_: *mut LeanObject,
    mut v___y_5503_: *mut LeanObject,
    mut v___y_5504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5505_: usize = 0;
    let mut v_i_boxed_5506_: usize = 0;
    let mut v_res_5507_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5505_ = lean_unbox_usize(v_sz_5493_);
    lean_dec(v_sz_5493_);
    v_i_boxed_5506_ = lean_unbox_usize(v_i_5494_);
    lean_dec(v_i_5494_);
    v_res_5507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_as_5492_, v_sz_boxed_5505_, v_i_boxed_5506_, v_b_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_);
    lean_dec(v___y_5503_);
    lean_dec_ref(v___y_5502_);
    lean_dec(v___y_5501_);
    lean_dec_ref(v___y_5500_);
    lean_dec(v___y_5499_);
    lean_dec_ref(v___y_5498_);
    lean_dec(v___y_5497_);
    lean_dec_ref(v___y_5496_);
    lean_dec_ref(v_as_5492_);
    return v_res_5507_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addExactSuggestions(
    mut v_ref_5513_: *mut LeanObject,
    mut v_es_5514_: *mut LeanObject,
    mut v_origSpan_x3f_5515_: *mut LeanObject,
    mut v_addSubgoalsMsg_5516_: u8,
    mut v_codeActionPrefix_x3f_5517_: *mut LeanObject,
    mut v_checkState_x3f_5518_: *mut LeanObject,
    mut v_tacticErrorAsInfo_5519_: u8,
    mut v_a_5520_: *mut LeanObject,
    mut v_a_5521_: *mut LeanObject,
    mut v_a_5522_: *mut LeanObject,
    mut v_a_5523_: *mut LeanObject,
    mut v_a_5524_: *mut LeanObject,
    mut v_a_5525_: *mut LeanObject,
    mut v_a_5526_: *mut LeanObject,
    mut v_a_5527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_5529_: usize = 0;
    let mut v___x_5530_: usize = 0;
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5534_: usize = 0;
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: u8 = 0;
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5544_: usize = 0;
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5548_: u8 = 0;
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5552_: u8 = 0;
    let mut v_unused_5553_: *mut LeanObject = core::ptr::null_mut();
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_5529_ = lean_array_size(v_es_5514_);
                v___x_5530_ = 0usize;
                v___x_5531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_5516_, v_checkState_x3f_5518_, v_sz_5529_, v___x_5530_, v_es_5514_, v_a_5520_, v_a_5521_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_);
                if lean_obj_tag(v___x_5531_) == 0 {
                    v_a_5532_ = lean_ctor_get(v___x_5531_, 0);
                    lean_inc(v_a_5532_);
                    lean_dec_ref_known(v___x_5531_, 1);
                    v___x_5533_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1;
                    v_sz_5534_ = lean_array_size(v_a_5532_);
                    v___x_5535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_5519_, v_a_5532_, v_sz_5534_, v___x_5530_, v___x_5533_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_);
                    lean_dec(v_a_5532_);
                    if lean_obj_tag(v___x_5535_) == 0 {
                        v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
                        lean_inc(v_a_5536_);
                        lean_dec_ref_known(v___x_5535_, 1);
                        v_fst_5537_ = lean_ctor_get(v_a_5536_, 0);
                        lean_inc(v_fst_5537_);
                        v_snd_5538_ = lean_ctor_get(v_a_5536_, 1);
                        lean_inc(v_snd_5538_);
                        lean_dec(v_a_5536_);
                        v___x_5539_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2;
                        v___x_5540_ = 4;
                        v___x_5541_ = l_Lean_MessageData_nil;
                        v___x_5542_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(
                            v_ref_5513_,
                            v_fst_5537_,
                            v_origSpan_x3f_5515_,
                            v___x_5539_,
                            v_codeActionPrefix_x3f_5517_,
                            v___x_5540_,
                            v___x_5541_,
                            v_a_5526_,
                            v_a_5527_,
                        );
                        if lean_obj_tag(v___x_5542_) == 0 {
                            lean_dec_ref_known(v___x_5542_, 1);
                            v___x_5543_ = lean_box(0);
                            v_sz_5544_ = lean_array_size(v_snd_5538_);
                            v___x_5545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_snd_5538_, v_sz_5544_, v___x_5530_, v___x_5543_, v_a_5520_, v_a_5521_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_);
                            lean_dec(v_snd_5538_);
                            if lean_obj_tag(v___x_5545_) == 0 {
                                v_isSharedCheck_5552_ = (!lean_is_exclusive(v___x_5545_)) as u8;
                                if v_isSharedCheck_5552_ == 0 {
                                    v_unused_5553_ = lean_ctor_get(v___x_5545_, 0);
                                    lean_dec(v_unused_5553_);
                                    v___x_5547_ = v___x_5545_;
                                    v_isShared_5548_ = v_isSharedCheck_5552_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___x_5545_);
                                    v___x_5547_ = lean_box(0);
                                    v_isShared_5548_ = v_isSharedCheck_5552_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                return v___x_5545_;
                            }
                        } else {
                            lean_dec(v_snd_5538_);
                            return v___x_5542_;
                        }
                    } else {
                        lean_dec(v_codeActionPrefix_x3f_5517_);
                        lean_dec(v_origSpan_x3f_5515_);
                        lean_dec(v_ref_5513_);
                        v_a_5554_ = lean_ctor_get(v___x_5535_, 0);
                        v_isSharedCheck_5561_ = (!lean_is_exclusive(v___x_5535_)) as u8;
                        if v_isSharedCheck_5561_ == 0 {
                            v___x_5556_ = v___x_5535_;
                            v_isShared_5557_ = v_isSharedCheck_5561_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5554_);
                            lean_dec(v___x_5535_);
                            v___x_5556_ = lean_box(0);
                            v_isShared_5557_ = v_isSharedCheck_5561_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_codeActionPrefix_x3f_5517_);
                    lean_dec(v_origSpan_x3f_5515_);
                    lean_dec(v_ref_5513_);
                    v_a_5562_ = lean_ctor_get(v___x_5531_, 0);
                    v_isSharedCheck_5569_ = (!lean_is_exclusive(v___x_5531_)) as u8;
                    if v_isSharedCheck_5569_ == 0 {
                        v___x_5564_ = v___x_5531_;
                        v_isShared_5565_ = v_isSharedCheck_5569_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5562_);
                        lean_dec(v___x_5531_);
                        v___x_5564_ = lean_box(0);
                        v_isShared_5565_ = v_isSharedCheck_5569_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5548_ == 0 {
                    lean_ctor_set(v___x_5547_, 0, v___x_5543_);
                    v___x_5550_ = v___x_5547_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5551_, 0, v___x_5543_);
                    v___x_5550_ = v_reuseFailAlloc_5551_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5550_;
            }
            3 => {
                if v_isShared_5557_ == 0 {
                    v___x_5559_ = v___x_5556_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5560_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5560_, 0, v_a_5554_);
                    v___x_5559_ = v_reuseFailAlloc_5560_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5559_;
            }
            5 => {
                if v_isShared_5565_ == 0 {
                    v___x_5567_ = v___x_5564_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5568_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_a_5562_);
                    v___x_5567_ = v_reuseFailAlloc_5568_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5567_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addExactSuggestions___boxed(
    mut v_ref_5570_: *mut LeanObject,
    mut v_es_5571_: *mut LeanObject,
    mut v_origSpan_x3f_5572_: *mut LeanObject,
    mut v_addSubgoalsMsg_5573_: *mut LeanObject,
    mut v_codeActionPrefix_x3f_5574_: *mut LeanObject,
    mut v_checkState_x3f_5575_: *mut LeanObject,
    mut v_tacticErrorAsInfo_5576_: *mut LeanObject,
    mut v_a_5577_: *mut LeanObject,
    mut v_a_5578_: *mut LeanObject,
    mut v_a_5579_: *mut LeanObject,
    mut v_a_5580_: *mut LeanObject,
    mut v_a_5581_: *mut LeanObject,
    mut v_a_5582_: *mut LeanObject,
    mut v_a_5583_: *mut LeanObject,
    mut v_a_5584_: *mut LeanObject,
    mut v_a_5585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_addSubgoalsMsg_boxed_5586_: u8 = 0;
    let mut v_tacticErrorAsInfo_boxed_5587_: u8 = 0;
    let mut v_res_5588_: *mut LeanObject = core::ptr::null_mut();
    v_addSubgoalsMsg_boxed_5586_ = (lean_unbox(v_addSubgoalsMsg_5573_) as u8);
    v_tacticErrorAsInfo_boxed_5587_ = (lean_unbox(v_tacticErrorAsInfo_5576_) as u8);
    v_res_5588_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestions(
        v_ref_5570_,
        v_es_5571_,
        v_origSpan_x3f_5572_,
        v_addSubgoalsMsg_boxed_5586_,
        v_codeActionPrefix_x3f_5574_,
        v_checkState_x3f_5575_,
        v_tacticErrorAsInfo_boxed_5587_,
        v_a_5577_,
        v_a_5578_,
        v_a_5579_,
        v_a_5580_,
        v_a_5581_,
        v_a_5582_,
        v_a_5583_,
        v_a_5584_,
    );
    lean_dec(v_a_5584_);
    lean_dec_ref(v_a_5583_);
    lean_dec(v_a_5582_);
    lean_dec_ref(v_a_5581_);
    lean_dec(v_a_5580_);
    lean_dec_ref(v_a_5579_);
    lean_dec(v_a_5578_);
    lean_dec_ref(v_a_5577_);
    return v_res_5588_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(
    mut v_tacticErrorAsInfo_5589_: u8,
    mut v_as_5590_: *mut LeanObject,
    mut v_sz_5591_: usize,
    mut v_i_5592_: usize,
    mut v_b_5593_: *mut LeanObject,
    mut v___y_5594_: *mut LeanObject,
    mut v___y_5595_: *mut LeanObject,
    mut v___y_5596_: *mut LeanObject,
    mut v___y_5597_: *mut LeanObject,
    mut v___y_5598_: *mut LeanObject,
    mut v___y_5599_: *mut LeanObject,
    mut v___y_5600_: *mut LeanObject,
    mut v___y_5601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    v___x_5603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_5589_, v_as_5590_, v_sz_5591_, v_i_5592_, v_b_5593_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_);
    return v___x_5603_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___boxed(
    mut v_tacticErrorAsInfo_5604_: *mut LeanObject,
    mut v_as_5605_: *mut LeanObject,
    mut v_sz_5606_: *mut LeanObject,
    mut v_i_5607_: *mut LeanObject,
    mut v_b_5608_: *mut LeanObject,
    mut v___y_5609_: *mut LeanObject,
    mut v___y_5610_: *mut LeanObject,
    mut v___y_5611_: *mut LeanObject,
    mut v___y_5612_: *mut LeanObject,
    mut v___y_5613_: *mut LeanObject,
    mut v___y_5614_: *mut LeanObject,
    mut v___y_5615_: *mut LeanObject,
    mut v___y_5616_: *mut LeanObject,
    mut v___y_5617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tacticErrorAsInfo_boxed_5618_: u8 = 0;
    let mut v_sz_boxed_5619_: usize = 0;
    let mut v_i_boxed_5620_: usize = 0;
    let mut v_res_5621_: *mut LeanObject = core::ptr::null_mut();
    v_tacticErrorAsInfo_boxed_5618_ = (lean_unbox(v_tacticErrorAsInfo_5604_) as u8);
    v_sz_boxed_5619_ = lean_unbox_usize(v_sz_5606_);
    lean_dec(v_sz_5606_);
    v_i_boxed_5620_ = lean_unbox_usize(v_i_5607_);
    lean_dec(v_i_5607_);
    v_res_5621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(v_tacticErrorAsInfo_boxed_5618_, v_as_5605_, v_sz_boxed_5619_, v_i_boxed_5620_, v_b_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_);
    lean_dec(v___y_5616_);
    lean_dec_ref(v___y_5615_);
    lean_dec(v___y_5614_);
    lean_dec_ref(v___y_5613_);
    lean_dec(v___y_5612_);
    lean_dec_ref(v___y_5611_);
    lean_dec(v___y_5610_);
    lean_dec_ref(v___y_5609_);
    lean_dec_ref(v_as_5605_);
    return v_res_5621_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addTermSuggestion(
    mut v_ref_5622_: *mut LeanObject,
    mut v_e_5623_: *mut LeanObject,
    mut v_origSpan_x3f_5624_: *mut LeanObject,
    mut v_header_5625_: *mut LeanObject,
    mut v_codeActionPrefix_x3f_5626_: *mut LeanObject,
    mut v_a_5627_: *mut LeanObject,
    mut v_a_5628_: *mut LeanObject,
    mut v_a_5629_: *mut LeanObject,
    mut v_a_5630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: u8 = 0;
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5640_: u8 = 0;
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5644_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5632_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(
                    v_e_5623_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_,
                );
                if lean_obj_tag(v___x_5632_) == 0 {
                    v_a_5633_ = lean_ctor_get(v___x_5632_, 0);
                    lean_inc(v_a_5633_);
                    lean_dec_ref_known(v___x_5632_, 1);
                    v___x_5634_ = 4;
                    v___x_5635_ = l_Lean_MessageData_nil;
                    v___x_5636_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                        v_ref_5622_,
                        v_a_5633_,
                        v_origSpan_x3f_5624_,
                        v_header_5625_,
                        v_codeActionPrefix_x3f_5626_,
                        v___x_5634_,
                        v___x_5635_,
                        v_a_5629_,
                        v_a_5630_,
                    );
                    return v___x_5636_;
                } else {
                    lean_dec(v_codeActionPrefix_x3f_5626_);
                    lean_dec_ref(v_header_5625_);
                    lean_dec(v_origSpan_x3f_5624_);
                    lean_dec(v_ref_5622_);
                    v_a_5637_ = lean_ctor_get(v___x_5632_, 0);
                    v_isSharedCheck_5644_ = (!lean_is_exclusive(v___x_5632_)) as u8;
                    if v_isSharedCheck_5644_ == 0 {
                        v___x_5639_ = v___x_5632_;
                        v_isShared_5640_ = v_isSharedCheck_5644_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5637_);
                        lean_dec(v___x_5632_);
                        v___x_5639_ = lean_box(0);
                        v_isShared_5640_ = v_isSharedCheck_5644_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5640_ == 0 {
                    v___x_5642_ = v___x_5639_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5643_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_a_5637_);
                    v___x_5642_ = v_reuseFailAlloc_5643_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addTermSuggestion___boxed(
    mut v_ref_5645_: *mut LeanObject,
    mut v_e_5646_: *mut LeanObject,
    mut v_origSpan_x3f_5647_: *mut LeanObject,
    mut v_header_5648_: *mut LeanObject,
    mut v_codeActionPrefix_x3f_5649_: *mut LeanObject,
    mut v_a_5650_: *mut LeanObject,
    mut v_a_5651_: *mut LeanObject,
    mut v_a_5652_: *mut LeanObject,
    mut v_a_5653_: *mut LeanObject,
    mut v_a_5654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5655_: *mut LeanObject = core::ptr::null_mut();
    v_res_5655_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestion(
        v_ref_5645_,
        v_e_5646_,
        v_origSpan_x3f_5647_,
        v_header_5648_,
        v_codeActionPrefix_x3f_5649_,
        v_a_5650_,
        v_a_5651_,
        v_a_5652_,
        v_a_5653_,
    );
    lean_dec(v_a_5653_);
    lean_dec_ref(v_a_5652_);
    lean_dec(v_a_5651_);
    lean_dec_ref(v_a_5650_);
    return v_res_5655_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(
    mut v_sz_5656_: usize,
    mut v_i_5657_: usize,
    mut v_bs_5658_: *mut LeanObject,
    mut v___y_5659_: *mut LeanObject,
    mut v___y_5660_: *mut LeanObject,
    mut v___y_5661_: *mut LeanObject,
    mut v___y_5662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5664_: u8 = 0;
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: usize = 0;
    let mut v___x_5672_: usize = 0;
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5678_: u8 = 0;
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5664_ = lean_usize_dec_lt(v_i_5657_, v_sz_5656_);
                if v___x_5664_ == 0 {
                    v___x_5665_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5665_, 0, v_bs_5658_);
                    return v___x_5665_;
                } else {
                    v_v_5666_ = lean_array_uget_borrowed(v_bs_5658_, v_i_5657_);
                    lean_inc(v_v_5666_);
                    v___x_5667_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(
                        v_v_5666_,
                        v___y_5659_,
                        v___y_5660_,
                        v___y_5661_,
                        v___y_5662_,
                    );
                    if lean_obj_tag(v___x_5667_) == 0 {
                        v_a_5668_ = lean_ctor_get(v___x_5667_, 0);
                        lean_inc(v_a_5668_);
                        lean_dec_ref_known(v___x_5667_, 1);
                        v___x_5669_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5670_ = lean_array_uset(v_bs_5658_, v_i_5657_, v___x_5669_);
                        v___x_5671_ = 1usize;
                        v___x_5672_ = lean_usize_add(v_i_5657_, v___x_5671_);
                        v___x_5673_ = lean_array_uset(v_bs_x27_5670_, v_i_5657_, v_a_5668_);
                        v_i_5657_ = v___x_5672_;
                        v_bs_5658_ = v___x_5673_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5658_);
                        v_a_5675_ = lean_ctor_get(v___x_5667_, 0);
                        v_isSharedCheck_5682_ = (!lean_is_exclusive(v___x_5667_)) as u8;
                        if v_isSharedCheck_5682_ == 0 {
                            v___x_5677_ = v___x_5667_;
                            v_isShared_5678_ = v_isSharedCheck_5682_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5675_);
                            lean_dec(v___x_5667_);
                            v___x_5677_ = lean_box(0);
                            v_isShared_5678_ = v_isSharedCheck_5682_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5678_ == 0 {
                    v___x_5680_ = v___x_5677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5681_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5681_, 0, v_a_5675_);
                    v___x_5680_ = v_reuseFailAlloc_5681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0___boxed(
    mut v_sz_5683_: *mut LeanObject,
    mut v_i_5684_: *mut LeanObject,
    mut v_bs_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
    mut v___y_5687_: *mut LeanObject,
    mut v___y_5688_: *mut LeanObject,
    mut v___y_5689_: *mut LeanObject,
    mut v___y_5690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5691_: usize = 0;
    let mut v_i_boxed_5692_: usize = 0;
    let mut v_res_5693_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5691_ = lean_unbox_usize(v_sz_5683_);
    lean_dec(v_sz_5683_);
    v_i_boxed_5692_ = lean_unbox_usize(v_i_5684_);
    lean_dec(v_i_5684_);
    v_res_5693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_boxed_5691_, v_i_boxed_5692_, v_bs_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_);
    lean_dec(v___y_5689_);
    lean_dec_ref(v___y_5688_);
    lean_dec(v___y_5687_);
    lean_dec_ref(v___y_5686_);
    return v_res_5693_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addTermSuggestions(
    mut v_ref_5694_: *mut LeanObject,
    mut v_es_5695_: *mut LeanObject,
    mut v_origSpan_x3f_5696_: *mut LeanObject,
    mut v_header_5697_: *mut LeanObject,
    mut v_codeActionPrefix_x3f_5698_: *mut LeanObject,
    mut v_a_5699_: *mut LeanObject,
    mut v_a_5700_: *mut LeanObject,
    mut v_a_5701_: *mut LeanObject,
    mut v_a_5702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_5704_: usize = 0;
    let mut v___x_5705_: usize = 0;
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: u8 = 0;
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5714_: u8 = 0;
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_5704_ = lean_array_size(v_es_5695_);
                v___x_5705_ = 0usize;
                v___x_5706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_5704_, v___x_5705_, v_es_5695_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
                if lean_obj_tag(v___x_5706_) == 0 {
                    v_a_5707_ = lean_ctor_get(v___x_5706_, 0);
                    lean_inc(v_a_5707_);
                    lean_dec_ref_known(v___x_5706_, 1);
                    v___x_5708_ = 4;
                    v___x_5709_ = l_Lean_MessageData_nil;
                    v___x_5710_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(
                        v_ref_5694_,
                        v_a_5707_,
                        v_origSpan_x3f_5696_,
                        v_header_5697_,
                        v_codeActionPrefix_x3f_5698_,
                        v___x_5708_,
                        v___x_5709_,
                        v_a_5701_,
                        v_a_5702_,
                    );
                    return v___x_5710_;
                } else {
                    lean_dec(v_codeActionPrefix_x3f_5698_);
                    lean_dec_ref(v_header_5697_);
                    lean_dec(v_origSpan_x3f_5696_);
                    lean_dec(v_ref_5694_);
                    v_a_5711_ = lean_ctor_get(v___x_5706_, 0);
                    v_isSharedCheck_5718_ = (!lean_is_exclusive(v___x_5706_)) as u8;
                    if v_isSharedCheck_5718_ == 0 {
                        v___x_5713_ = v___x_5706_;
                        v_isShared_5714_ = v_isSharedCheck_5718_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5711_);
                        lean_dec(v___x_5706_);
                        v___x_5713_ = lean_box(0);
                        v_isShared_5714_ = v_isSharedCheck_5718_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5714_ == 0 {
                    v___x_5716_ = v___x_5713_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5717_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5717_, 0, v_a_5711_);
                    v___x_5716_ = v_reuseFailAlloc_5717_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addTermSuggestions___boxed(
    mut v_ref_5719_: *mut LeanObject,
    mut v_es_5720_: *mut LeanObject,
    mut v_origSpan_x3f_5721_: *mut LeanObject,
    mut v_header_5722_: *mut LeanObject,
    mut v_codeActionPrefix_x3f_5723_: *mut LeanObject,
    mut v_a_5724_: *mut LeanObject,
    mut v_a_5725_: *mut LeanObject,
    mut v_a_5726_: *mut LeanObject,
    mut v_a_5727_: *mut LeanObject,
    mut v_a_5728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5729_: *mut LeanObject = core::ptr::null_mut();
    v_res_5729_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestions(
        v_ref_5719_,
        v_es_5720_,
        v_origSpan_x3f_5721_,
        v_header_5722_,
        v_codeActionPrefix_x3f_5723_,
        v_a_5724_,
        v_a_5725_,
        v_a_5726_,
        v_a_5727_,
    );
    lean_dec(v_a_5727_);
    lean_dec_ref(v_a_5726_);
    lean_dec(v_a_5725_);
    lean_dec_ref(v_a_5724_);
    return v_res_5729_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6()
-> *mut LeanObject {
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    v___x_5744_ = l_Array_mkArray0(lean_box(0));
    return v___x_5744_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15()
-> *mut LeanObject {
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    v___x_5765_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__14;
    v___x_5766_ = l_Lean_stringToMessageData(v___x_5765_);
    return v___x_5766_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17()
-> *mut LeanObject {
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut LeanObject = core::ptr::null_mut();
    v___x_5768_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__16;
    v___x_5769_ = l_Lean_stringToMessageData(v___x_5768_);
    return v___x_5769_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22()
-> *mut LeanObject {
    let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    v___x_5778_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__21;
    v___x_5779_ = l_Lean_stringToMessageData(v___x_5778_);
    return v___x_5779_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30()
-> *mut LeanObject {
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    v___x_5793_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0;
    v___x_5794_ = l_String_toRawSubstring_x27(v___x_5793_);
    return v___x_5794_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81()
-> *mut LeanObject {
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    v___x_5932_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__80;
    v___x_5933_ = l_Lean_stringToMessageData(v___x_5932_);
    return v___x_5933_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83()
-> *mut LeanObject {
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    v___x_5935_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__82;
    v___x_5936_ = l_Lean_stringToMessageData(v___x_5935_);
    return v___x_5936_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85()
-> *mut LeanObject {
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    v___x_5938_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__84;
    v___x_5939_ = l_Lean_stringToMessageData(v___x_5938_);
    return v___x_5939_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(
    mut v_e_5940_: *mut LeanObject,
    mut v_t_x3f_5941_: *mut LeanObject,
    mut v_a_5942_: u8,
    mut v_h_x3f_5943_: *mut LeanObject,
    mut v___y_5944_: *mut LeanObject,
    mut v___y_5945_: *mut LeanObject,
    mut v___y_5946_: *mut LeanObject,
    mut v___y_5947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5960_: u8 = 0;
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5965_: u8 = 0;
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_a_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: u8 = 0;
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: u8 = 0;
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6122_: u8 = 0;
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6126_: u8 = 0;
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: u8 = 0;
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: u8 = 0;
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6193_: u8 = 0;
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_5940_);
                v___x_5966_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(
                    v_e_5940_,
                    v___y_5944_,
                    v___y_5945_,
                    v___y_5946_,
                    v___y_5947_,
                );
                if lean_obj_tag(v___x_5966_) == 0 {
                    v_a_5967_ = lean_ctor_get(v___x_5966_, 0);
                    lean_inc(v_a_5967_);
                    lean_dec_ref_known(v___x_5966_, 1);
                    if lean_obj_tag(v_t_x3f_5941_) == 1 {
                        v_val_5997_ = lean_ctor_get(v_t_x3f_5941_, 0);
                        lean_inc_n(v_val_5997_, 2);
                        lean_dec_ref_known(v_t_x3f_5941_, 1);
                        v___x_5998_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(
                            v_val_5997_,
                            v___y_5944_,
                            v___y_5945_,
                            v___y_5946_,
                            v___y_5947_,
                        );
                        if lean_obj_tag(v___x_5998_) == 0 {
                            v_a_5999_ = lean_ctor_get(v___x_5998_, 0);
                            lean_inc(v_a_5999_);
                            lean_dec_ref_known(v___x_5998_, 1);
                            if v_a_5942_ == 0 {
                                if lean_obj_tag(v_h_x3f_5943_) == 0 {
                                    v___x_6038_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24;
                                    v___y_6001_ = v___x_6038_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_val_6039_ = lean_ctor_get(v_h_x3f_5943_, 0);
                                    lean_inc(v_val_6039_);
                                    lean_dec_ref_known(v_h_x3f_5943_, 1);
                                    v___y_6001_ = v_val_6039_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                if lean_obj_tag(v_h_x3f_5943_) == 0 {
                                    v_ref_6040_ = lean_ctor_get(v___y_5946_, 5);
                                    v_quotContext_6041_ = lean_ctor_get(v___y_5946_, 10);
                                    v_currMacroScope_6042_ = lean_ctor_get(v___y_5946_, 11);
                                    v___x_6043_ = 0;
                                    v___x_6044_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_6040_, v___x_6043_);
                                    v___x_6045_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26;
                                    v___x_6046_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27;
                                    lean_inc_n(v___x_6044_, 12);
                                    v___x_6047_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_6047_, 0, v___x_6044_);
                                    lean_ctor_set(v___x_6047_, 1, v___x_6046_);
                                    v___x_6048_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5;
                                    v___x_6049_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
                                    v___x_6050_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
                                    v___x_6051_ = lean_alloc_ctor(1, 3, (0) as u32);
                                    lean_ctor_set(v___x_6051_, 0, v___x_6044_);
                                    lean_ctor_set(v___x_6051_, 1, v___x_6049_);
                                    lean_ctor_set(v___x_6051_, 2, v___x_6050_);
                                    lean_inc_ref(v___x_6051_);
                                    v___x_6052_ =
                                        l_Lean_Syntax_node1(v___x_6044_, v___x_6048_, v___x_6051_);
                                    v___x_6053_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8;
                                    v___x_6054_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10;
                                    v___x_6055_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12;
                                    v___x_6056_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29;
                                    v___x_6057_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30);
                                    v___x_6058_ = lean_box(0);
                                    lean_inc(v_currMacroScope_6042_);
                                    lean_inc(v_quotContext_6041_);
                                    v___x_6059_ = l_Lean_addMacroScope(
                                        v_quotContext_6041_,
                                        v___x_6058_,
                                        v_currMacroScope_6042_,
                                    );
                                    v___x_6060_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79;
                                    v___x_6061_ = lean_alloc_ctor(3, 4, (0) as u32);
                                    lean_ctor_set(v___x_6061_, 0, v___x_6044_);
                                    lean_ctor_set(v___x_6061_, 1, v___x_6057_);
                                    lean_ctor_set(v___x_6061_, 2, v___x_6059_);
                                    lean_ctor_set(v___x_6061_, 3, v___x_6060_);
                                    v___x_6062_ =
                                        l_Lean_Syntax_node1(v___x_6044_, v___x_6056_, v___x_6061_);
                                    v___x_6063_ =
                                        l_Lean_Syntax_node1(v___x_6044_, v___x_6055_, v___x_6062_);
                                    v___x_6064_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19;
                                    v___x_6065_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20;
                                    v___x_6066_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_6066_, 0, v___x_6044_);
                                    lean_ctor_set(v___x_6066_, 1, v___x_6065_);
                                    v___x_6067_ = l_Lean_Syntax_node2(
                                        v___x_6044_,
                                        v___x_6064_,
                                        v___x_6066_,
                                        v_a_5999_,
                                    );
                                    v___x_6068_ =
                                        l_Lean_Syntax_node1(v___x_6044_, v___x_6049_, v___x_6067_);
                                    v___x_6069_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13;
                                    v___x_6070_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_6070_, 0, v___x_6044_);
                                    lean_ctor_set(v___x_6070_, 1, v___x_6069_);
                                    v___x_6071_ = l_Lean_Syntax_node5(
                                        v___x_6044_,
                                        v___x_6054_,
                                        v___x_6063_,
                                        v___x_6051_,
                                        v___x_6068_,
                                        v___x_6070_,
                                        v_a_5967_,
                                    );
                                    v___x_6072_ =
                                        l_Lean_Syntax_node1(v___x_6044_, v___x_6053_, v___x_6071_);
                                    v___x_6073_ = l_Lean_Syntax_node3(
                                        v___x_6044_,
                                        v___x_6045_,
                                        v___x_6047_,
                                        v___x_6052_,
                                        v___x_6072_,
                                    );
                                    v___x_6074_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81);
                                    v___x_6075_ = l_Lean_MessageData_ofExpr(v_val_5997_);
                                    v___x_6076_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_6076_, 0, v___x_6074_);
                                    lean_ctor_set(v___x_6076_, 1, v___x_6075_);
                                    v___x_6077_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
                                    v___x_6078_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_6078_, 0, v___x_6076_);
                                    lean_ctor_set(v___x_6078_, 1, v___x_6077_);
                                    v___x_6079_ = l_Lean_MessageData_ofExpr(v_e_5940_);
                                    v___x_6080_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_6080_, 0, v___x_6078_);
                                    lean_ctor_set(v___x_6080_, 1, v___x_6079_);
                                    v_fst_5950_ = v___x_6073_;
                                    v_snd_5951_ = v___x_6080_;
                                    v___y_5952_ = v___y_5944_;
                                    v___y_5953_ = v___y_5945_;
                                    v___y_5954_ = v___y_5946_;
                                    v___y_5955_ = v___y_5947_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_6081_ = lean_ctor_get(v_h_x3f_5943_, 0);
                                    lean_inc_n(v_val_6081_, 2);
                                    lean_dec_ref_known(v_h_x3f_5943_, 1);
                                    v_ref_6082_ = lean_ctor_get(v___y_5946_, 5);
                                    v___x_6083_ = 0;
                                    v___x_6084_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_6082_, v___x_6083_);
                                    v___x_6085_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26;
                                    v___x_6086_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27;
                                    lean_inc_n(v___x_6084_, 10);
                                    v___x_6087_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_6087_, 0, v___x_6084_);
                                    lean_ctor_set(v___x_6087_, 1, v___x_6086_);
                                    v___x_6088_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5;
                                    v___x_6089_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
                                    v___x_6090_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
                                    v___x_6091_ = lean_alloc_ctor(1, 3, (0) as u32);
                                    lean_ctor_set(v___x_6091_, 0, v___x_6084_);
                                    lean_ctor_set(v___x_6091_, 1, v___x_6089_);
                                    lean_ctor_set(v___x_6091_, 2, v___x_6090_);
                                    lean_inc_ref(v___x_6091_);
                                    v___x_6092_ =
                                        l_Lean_Syntax_node1(v___x_6084_, v___x_6088_, v___x_6091_);
                                    v___x_6093_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8;
                                    v___x_6094_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10;
                                    v___x_6095_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12;
                                    v___x_6096_ = lean_mk_syntax_ident(v_val_6081_);
                                    v___x_6097_ =
                                        l_Lean_Syntax_node1(v___x_6084_, v___x_6095_, v___x_6096_);
                                    v___x_6098_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19;
                                    v___x_6099_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20;
                                    v___x_6100_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_6100_, 0, v___x_6084_);
                                    lean_ctor_set(v___x_6100_, 1, v___x_6099_);
                                    v___x_6101_ = l_Lean_Syntax_node2(
                                        v___x_6084_,
                                        v___x_6098_,
                                        v___x_6100_,
                                        v_a_5999_,
                                    );
                                    v___x_6102_ =
                                        l_Lean_Syntax_node1(v___x_6084_, v___x_6089_, v___x_6101_);
                                    v___x_6103_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13;
                                    v___x_6104_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_6104_, 0, v___x_6084_);
                                    lean_ctor_set(v___x_6104_, 1, v___x_6103_);
                                    v___x_6105_ = l_Lean_Syntax_node5(
                                        v___x_6084_,
                                        v___x_6094_,
                                        v___x_6097_,
                                        v___x_6091_,
                                        v___x_6102_,
                                        v___x_6104_,
                                        v_a_5967_,
                                    );
                                    v___x_6106_ =
                                        l_Lean_Syntax_node1(v___x_6084_, v___x_6093_, v___x_6105_);
                                    v___x_6107_ = l_Lean_Syntax_node3(
                                        v___x_6084_,
                                        v___x_6085_,
                                        v___x_6087_,
                                        v___x_6092_,
                                        v___x_6106_,
                                    );
                                    v___x_6108_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83);
                                    v___x_6109_ = l_Lean_MessageData_ofName(v_val_6081_);
                                    v___x_6110_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_6110_, 0, v___x_6108_);
                                    lean_ctor_set(v___x_6110_, 1, v___x_6109_);
                                    v___x_6111_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22);
                                    v___x_6112_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_6112_, 0, v___x_6110_);
                                    lean_ctor_set(v___x_6112_, 1, v___x_6111_);
                                    v___x_6113_ = l_Lean_MessageData_ofExpr(v_val_5997_);
                                    v___x_6114_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_6114_, 0, v___x_6112_);
                                    lean_ctor_set(v___x_6114_, 1, v___x_6113_);
                                    v___x_6115_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
                                    v___x_6116_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_6116_, 0, v___x_6114_);
                                    lean_ctor_set(v___x_6116_, 1, v___x_6115_);
                                    v___x_6117_ = l_Lean_MessageData_ofExpr(v_e_5940_);
                                    v___x_6118_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_6118_, 0, v___x_6116_);
                                    lean_ctor_set(v___x_6118_, 1, v___x_6117_);
                                    v_fst_5950_ = v___x_6107_;
                                    v_snd_5951_ = v___x_6118_;
                                    v___y_5952_ = v___y_5944_;
                                    v___y_5953_ = v___y_5945_;
                                    v___y_5954_ = v___y_5946_;
                                    v___y_5955_ = v___y_5947_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_5997_);
                            lean_dec(v_a_5967_);
                            lean_dec_ref(v___y_5946_);
                            lean_dec(v_h_x3f_5943_);
                            lean_dec_ref(v_e_5940_);
                            v_a_6119_ = lean_ctor_get(v___x_5998_, 0);
                            v_isSharedCheck_6126_ = (!lean_is_exclusive(v___x_5998_)) as u8;
                            if v_isSharedCheck_6126_ == 0 {
                                v___x_6121_ = v___x_5998_;
                                v_isShared_6122_ = v_isSharedCheck_6126_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_6119_);
                                lean_dec(v___x_5998_);
                                v___x_6121_ = lean_box(0);
                                v_isShared_6122_ = v_isSharedCheck_6126_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_t_x3f_5941_);
                        if v_a_5942_ == 0 {
                            if lean_obj_tag(v_h_x3f_5943_) == 0 {
                                v___x_6127_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24;
                                v___y_5969_ = v___x_6127_;
                                state = 4;
                                continue;
                            } else {
                                v_val_6128_ = lean_ctor_get(v_h_x3f_5943_, 0);
                                lean_inc(v_val_6128_);
                                lean_dec_ref_known(v_h_x3f_5943_, 1);
                                v___y_5969_ = v_val_6128_;
                                state = 4;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v_h_x3f_5943_) == 0 {
                                v_ref_6129_ = lean_ctor_get(v___y_5946_, 5);
                                v_quotContext_6130_ = lean_ctor_get(v___y_5946_, 10);
                                v_currMacroScope_6131_ = lean_ctor_get(v___y_5946_, 11);
                                v___x_6132_ = 0;
                                v___x_6133_ = l_Lean_SourceInfo_fromRef(v_ref_6129_, v___x_6132_);
                                v___x_6134_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26;
                                v___x_6135_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27;
                                lean_inc_n(v___x_6133_, 9);
                                v___x_6136_ = lean_alloc_ctor(2, 2, (0) as u32);
                                lean_ctor_set(v___x_6136_, 0, v___x_6133_);
                                lean_ctor_set(v___x_6136_, 1, v___x_6135_);
                                v___x_6137_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5;
                                v___x_6138_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
                                v___x_6139_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
                                v___x_6140_ = lean_alloc_ctor(1, 3, (0) as u32);
                                lean_ctor_set(v___x_6140_, 0, v___x_6133_);
                                lean_ctor_set(v___x_6140_, 1, v___x_6138_);
                                lean_ctor_set(v___x_6140_, 2, v___x_6139_);
                                lean_inc_ref_n(v___x_6140_, 2);
                                v___x_6141_ =
                                    l_Lean_Syntax_node1(v___x_6133_, v___x_6137_, v___x_6140_);
                                v___x_6142_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8;
                                v___x_6143_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10;
                                v___x_6144_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12;
                                v___x_6145_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29;
                                v___x_6146_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30);
                                v___x_6147_ = lean_box(0);
                                lean_inc(v_currMacroScope_6131_);
                                lean_inc(v_quotContext_6130_);
                                v___x_6148_ = l_Lean_addMacroScope(
                                    v_quotContext_6130_,
                                    v___x_6147_,
                                    v_currMacroScope_6131_,
                                );
                                v___x_6149_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79;
                                v___x_6150_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_6150_, 0, v___x_6133_);
                                lean_ctor_set(v___x_6150_, 1, v___x_6146_);
                                lean_ctor_set(v___x_6150_, 2, v___x_6148_);
                                lean_ctor_set(v___x_6150_, 3, v___x_6149_);
                                v___x_6151_ =
                                    l_Lean_Syntax_node1(v___x_6133_, v___x_6145_, v___x_6150_);
                                v___x_6152_ =
                                    l_Lean_Syntax_node1(v___x_6133_, v___x_6144_, v___x_6151_);
                                v___x_6153_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13;
                                v___x_6154_ = lean_alloc_ctor(2, 2, (0) as u32);
                                lean_ctor_set(v___x_6154_, 0, v___x_6133_);
                                lean_ctor_set(v___x_6154_, 1, v___x_6153_);
                                v___x_6155_ = l_Lean_Syntax_node5(
                                    v___x_6133_,
                                    v___x_6143_,
                                    v___x_6152_,
                                    v___x_6140_,
                                    v___x_6140_,
                                    v___x_6154_,
                                    v_a_5967_,
                                );
                                v___x_6156_ =
                                    l_Lean_Syntax_node1(v___x_6133_, v___x_6142_, v___x_6155_);
                                v___x_6157_ = l_Lean_Syntax_node3(
                                    v___x_6133_,
                                    v___x_6134_,
                                    v___x_6136_,
                                    v___x_6141_,
                                    v___x_6156_,
                                );
                                v___x_6158_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85);
                                v___x_6159_ = l_Lean_MessageData_ofExpr(v_e_5940_);
                                v___x_6160_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6160_, 0, v___x_6158_);
                                lean_ctor_set(v___x_6160_, 1, v___x_6159_);
                                v_fst_5950_ = v___x_6157_;
                                v_snd_5951_ = v___x_6160_;
                                v___y_5952_ = v___y_5944_;
                                v___y_5953_ = v___y_5945_;
                                v___y_5954_ = v___y_5946_;
                                v___y_5955_ = v___y_5947_;
                                state = 1;
                                continue;
                            } else {
                                v_val_6161_ = lean_ctor_get(v_h_x3f_5943_, 0);
                                lean_inc_n(v_val_6161_, 2);
                                lean_dec_ref_known(v_h_x3f_5943_, 1);
                                v_ref_6162_ = lean_ctor_get(v___y_5946_, 5);
                                v___x_6163_ = 0;
                                v___x_6164_ = l_Lean_SourceInfo_fromRef(v_ref_6162_, v___x_6163_);
                                v___x_6165_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26;
                                v___x_6166_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27;
                                lean_inc_n(v___x_6164_, 7);
                                v___x_6167_ = lean_alloc_ctor(2, 2, (0) as u32);
                                lean_ctor_set(v___x_6167_, 0, v___x_6164_);
                                lean_ctor_set(v___x_6167_, 1, v___x_6166_);
                                v___x_6168_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5;
                                v___x_6169_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
                                v___x_6170_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
                                v___x_6171_ = lean_alloc_ctor(1, 3, (0) as u32);
                                lean_ctor_set(v___x_6171_, 0, v___x_6164_);
                                lean_ctor_set(v___x_6171_, 1, v___x_6169_);
                                lean_ctor_set(v___x_6171_, 2, v___x_6170_);
                                lean_inc_ref_n(v___x_6171_, 2);
                                v___x_6172_ =
                                    l_Lean_Syntax_node1(v___x_6164_, v___x_6168_, v___x_6171_);
                                v___x_6173_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8;
                                v___x_6174_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10;
                                v___x_6175_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12;
                                v___x_6176_ = lean_mk_syntax_ident(v_val_6161_);
                                v___x_6177_ =
                                    l_Lean_Syntax_node1(v___x_6164_, v___x_6175_, v___x_6176_);
                                v___x_6178_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13;
                                v___x_6179_ = lean_alloc_ctor(2, 2, (0) as u32);
                                lean_ctor_set(v___x_6179_, 0, v___x_6164_);
                                lean_ctor_set(v___x_6179_, 1, v___x_6178_);
                                v___x_6180_ = l_Lean_Syntax_node5(
                                    v___x_6164_,
                                    v___x_6174_,
                                    v___x_6177_,
                                    v___x_6171_,
                                    v___x_6171_,
                                    v___x_6179_,
                                    v_a_5967_,
                                );
                                v___x_6181_ =
                                    l_Lean_Syntax_node1(v___x_6164_, v___x_6173_, v___x_6180_);
                                v___x_6182_ = l_Lean_Syntax_node3(
                                    v___x_6164_,
                                    v___x_6165_,
                                    v___x_6167_,
                                    v___x_6172_,
                                    v___x_6181_,
                                );
                                v___x_6183_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83);
                                v___x_6184_ = l_Lean_MessageData_ofName(v_val_6161_);
                                v___x_6185_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6185_, 0, v___x_6183_);
                                lean_ctor_set(v___x_6185_, 1, v___x_6184_);
                                v___x_6186_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
                                v___x_6187_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6187_, 0, v___x_6185_);
                                lean_ctor_set(v___x_6187_, 1, v___x_6186_);
                                v___x_6188_ = l_Lean_MessageData_ofExpr(v_e_5940_);
                                v___x_6189_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6189_, 0, v___x_6187_);
                                lean_ctor_set(v___x_6189_, 1, v___x_6188_);
                                v_fst_5950_ = v___x_6182_;
                                v_snd_5951_ = v___x_6189_;
                                v___y_5952_ = v___y_5944_;
                                v___y_5953_ = v___y_5945_;
                                v___y_5954_ = v___y_5946_;
                                v___y_5955_ = v___y_5947_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___y_5946_);
                    lean_dec(v_h_x3f_5943_);
                    lean_dec(v_t_x3f_5941_);
                    lean_dec_ref(v_e_5940_);
                    v_a_6190_ = lean_ctor_get(v___x_5966_, 0);
                    v_isSharedCheck_6197_ = (!lean_is_exclusive(v___x_5966_)) as u8;
                    if v_isSharedCheck_6197_ == 0 {
                        v___x_6192_ = v___x_5966_;
                        v_isShared_6193_ = v_isSharedCheck_6197_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6190_);
                        lean_dec(v___x_5966_);
                        v___x_6192_ = lean_box(0);
                        v_isShared_6193_ = v_isSharedCheck_6197_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5956_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_snd_5951_, v___y_5952_, v___y_5953_, v___y_5954_, v___y_5955_);
                lean_dec_ref(v___y_5954_);
                v_a_5957_ = lean_ctor_get(v___x_5956_, 0);
                v_isSharedCheck_5965_ = (!lean_is_exclusive(v___x_5956_)) as u8;
                if v_isSharedCheck_5965_ == 0 {
                    v___x_5959_ = v___x_5956_;
                    v_isShared_5960_ = v_isSharedCheck_5965_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_5957_);
                    lean_dec(v___x_5956_);
                    v___x_5959_ = lean_box(0);
                    v_isShared_5960_ = v_isSharedCheck_5965_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5961_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5961_, 0, v_fst_5950_);
                lean_ctor_set(v___x_5961_, 1, v_a_5957_);
                if v_isShared_5960_ == 0 {
                    lean_ctor_set(v___x_5959_, 0, v___x_5961_);
                    v___x_5963_ = v___x_5959_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5964_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5964_, 0, v___x_5961_);
                    v___x_5963_ = v_reuseFailAlloc_5964_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5963_;
            }
            4 => {
                v_ref_5970_ = lean_ctor_get(v___y_5946_, 5);
                v___x_5971_ = l_Lean_SourceInfo_fromRef(v_ref_5970_, v_a_5942_);
                v___x_5972_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1;
                v___x_5973_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2;
                lean_inc_n(v___x_5971_, 7);
                v___x_5974_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5974_, 0, v___x_5971_);
                lean_ctor_set(v___x_5974_, 1, v___x_5973_);
                v___x_5975_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5;
                v___x_5976_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
                v___x_5977_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6,
                );
                v___x_5978_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5978_, 0, v___x_5971_);
                lean_ctor_set(v___x_5978_, 1, v___x_5976_);
                lean_ctor_set(v___x_5978_, 2, v___x_5977_);
                lean_inc_ref_n(v___x_5978_, 2);
                v___x_5979_ = l_Lean_Syntax_node1(v___x_5971_, v___x_5975_, v___x_5978_);
                v___x_5980_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8;
                v___x_5981_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10;
                v___x_5982_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12;
                lean_inc(v___y_5969_);
                v___x_5983_ = lean_mk_syntax_ident(v___y_5969_);
                v___x_5984_ = l_Lean_Syntax_node1(v___x_5971_, v___x_5982_, v___x_5983_);
                v___x_5985_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13;
                v___x_5986_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5986_, 0, v___x_5971_);
                lean_ctor_set(v___x_5986_, 1, v___x_5985_);
                v___x_5987_ = l_Lean_Syntax_node5(
                    v___x_5971_,
                    v___x_5981_,
                    v___x_5984_,
                    v___x_5978_,
                    v___x_5978_,
                    v___x_5986_,
                    v_a_5967_,
                );
                v___x_5988_ = l_Lean_Syntax_node1(v___x_5971_, v___x_5980_, v___x_5987_);
                v___x_5989_ = l_Lean_Syntax_node3(
                    v___x_5971_,
                    v___x_5972_,
                    v___x_5974_,
                    v___x_5979_,
                    v___x_5988_,
                );
                v___x_5990_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15,
                );
                v___x_5991_ = l_Lean_MessageData_ofName(v___y_5969_);
                v___x_5992_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5992_, 0, v___x_5990_);
                lean_ctor_set(v___x_5992_, 1, v___x_5991_);
                v___x_5993_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17,
                );
                v___x_5994_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5994_, 0, v___x_5992_);
                lean_ctor_set(v___x_5994_, 1, v___x_5993_);
                v___x_5995_ = l_Lean_MessageData_ofExpr(v_e_5940_);
                v___x_5996_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5996_, 0, v___x_5994_);
                lean_ctor_set(v___x_5996_, 1, v___x_5995_);
                v_fst_5950_ = v___x_5989_;
                v_snd_5951_ = v___x_5996_;
                v___y_5952_ = v___y_5944_;
                v___y_5953_ = v___y_5945_;
                v___y_5954_ = v___y_5946_;
                v___y_5955_ = v___y_5947_;
                state = 1;
                continue;
            }
            5 => {
                v_ref_6002_ = lean_ctor_get(v___y_5946_, 5);
                v___x_6003_ = l_Lean_SourceInfo_fromRef(v_ref_6002_, v_a_5942_);
                v___x_6004_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1;
                v___x_6005_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2;
                lean_inc_n(v___x_6003_, 10);
                v___x_6006_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6006_, 0, v___x_6003_);
                lean_ctor_set(v___x_6006_, 1, v___x_6005_);
                v___x_6007_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5;
                v___x_6008_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
                v___x_6009_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6,
                );
                v___x_6010_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6010_, 0, v___x_6003_);
                lean_ctor_set(v___x_6010_, 1, v___x_6008_);
                lean_ctor_set(v___x_6010_, 2, v___x_6009_);
                lean_inc_ref(v___x_6010_);
                v___x_6011_ = l_Lean_Syntax_node1(v___x_6003_, v___x_6007_, v___x_6010_);
                v___x_6012_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8;
                v___x_6013_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10;
                v___x_6014_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12;
                lean_inc(v___y_6001_);
                v___x_6015_ = lean_mk_syntax_ident(v___y_6001_);
                v___x_6016_ = l_Lean_Syntax_node1(v___x_6003_, v___x_6014_, v___x_6015_);
                v___x_6017_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19;
                v___x_6018_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20;
                v___x_6019_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6019_, 0, v___x_6003_);
                lean_ctor_set(v___x_6019_, 1, v___x_6018_);
                v___x_6020_ = l_Lean_Syntax_node2(v___x_6003_, v___x_6017_, v___x_6019_, v_a_5999_);
                v___x_6021_ = l_Lean_Syntax_node1(v___x_6003_, v___x_6008_, v___x_6020_);
                v___x_6022_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13;
                v___x_6023_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6023_, 0, v___x_6003_);
                lean_ctor_set(v___x_6023_, 1, v___x_6022_);
                v___x_6024_ = l_Lean_Syntax_node5(
                    v___x_6003_,
                    v___x_6013_,
                    v___x_6016_,
                    v___x_6010_,
                    v___x_6021_,
                    v___x_6023_,
                    v_a_5967_,
                );
                v___x_6025_ = l_Lean_Syntax_node1(v___x_6003_, v___x_6012_, v___x_6024_);
                v___x_6026_ = l_Lean_Syntax_node3(
                    v___x_6003_,
                    v___x_6004_,
                    v___x_6006_,
                    v___x_6011_,
                    v___x_6025_,
                );
                v___x_6027_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15,
                );
                v___x_6028_ = l_Lean_MessageData_ofName(v___y_6001_);
                v___x_6029_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6029_, 0, v___x_6027_);
                lean_ctor_set(v___x_6029_, 1, v___x_6028_);
                v___x_6030_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22,
                );
                v___x_6031_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6031_, 0, v___x_6029_);
                lean_ctor_set(v___x_6031_, 1, v___x_6030_);
                v___x_6032_ = l_Lean_MessageData_ofExpr(v_val_5997_);
                v___x_6033_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6033_, 0, v___x_6031_);
                lean_ctor_set(v___x_6033_, 1, v___x_6032_);
                v___x_6034_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17,
                );
                v___x_6035_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6035_, 0, v___x_6033_);
                lean_ctor_set(v___x_6035_, 1, v___x_6034_);
                v___x_6036_ = l_Lean_MessageData_ofExpr(v_e_5940_);
                v___x_6037_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6037_, 0, v___x_6035_);
                lean_ctor_set(v___x_6037_, 1, v___x_6036_);
                v_fst_5950_ = v___x_6026_;
                v_snd_5951_ = v___x_6037_;
                v___y_5952_ = v___y_5944_;
                v___y_5953_ = v___y_5945_;
                v___y_5954_ = v___y_5946_;
                v___y_5955_ = v___y_5947_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_6122_ == 0 {
                    v___x_6124_ = v___x_6121_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6125_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6125_, 0, v_a_6119_);
                    v___x_6124_ = v_reuseFailAlloc_6125_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6124_;
            }
            8 => {
                if v_isShared_6193_ == 0 {
                    v___x_6195_ = v___x_6192_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6196_, 0, v_a_6190_);
                    v___x_6195_ = v_reuseFailAlloc_6196_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed(
    mut v_e_6198_: *mut LeanObject,
    mut v_t_x3f_6199_: *mut LeanObject,
    mut v_a_6200_: *mut LeanObject,
    mut v_h_x3f_6201_: *mut LeanObject,
    mut v___y_6202_: *mut LeanObject,
    mut v___y_6203_: *mut LeanObject,
    mut v___y_6204_: *mut LeanObject,
    mut v___y_6205_: *mut LeanObject,
    mut v___y_6206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_17939__boxed_6207_: u8 = 0;
    let mut v_res_6208_: *mut LeanObject = core::ptr::null_mut();
    v_a_17939__boxed_6207_ = (lean_unbox(v_a_6200_) as u8);
    v_res_6208_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(
        v_e_6198_,
        v_t_x3f_6199_,
        v_a_17939__boxed_6207_,
        v_h_x3f_6201_,
        v___y_6202_,
        v___y_6203_,
        v___y_6204_,
        v___y_6205_,
    );
    lean_dec(v___y_6205_);
    lean_dec(v___y_6203_);
    lean_dec_ref(v___y_6202_);
    return v_res_6208_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2() -> *mut LeanObject {
    let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut LeanObject = core::ptr::null_mut();
    v___x_6212_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1;
    v___x_6213_ = l_Lean_MessageData_ofFormat(v___x_6212_);
    return v___x_6213_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(
    mut v_ref_6214_: *mut LeanObject,
    mut v_h_x3f_6215_: *mut LeanObject,
    mut v_t_x3f_6216_: *mut LeanObject,
    mut v_e_6217_: *mut LeanObject,
    mut v_origSpan_x3f_6218_: *mut LeanObject,
    mut v_checkState_x3f_6219_: *mut LeanObject,
    mut v_a_6220_: *mut LeanObject,
    mut v_a_6221_: *mut LeanObject,
    mut v_a_6222_: *mut LeanObject,
    mut v_a_6223_: *mut LeanObject,
    mut v_a_6224_: *mut LeanObject,
    mut v_a_6225_: *mut LeanObject,
    mut v_a_6226_: *mut LeanObject,
    mut v_a_6227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tac_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: u8 = 0;
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6264_: u8 = 0;
    let mut v___x_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6269_: u8 = 0;
    let mut v_unused_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6274_: u8 = 0;
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6278_: u8 = 0;
    let mut v_fst_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6284_: u8 = 0;
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6288_: u8 = 0;
    let mut v_a_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6292_: u8 = 0;
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6296_: u8 = 0;
    let mut v_a_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6300_: u8 = 0;
    let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_6227_);
                lean_inc_ref(v_a_6226_);
                lean_inc(v_a_6225_);
                lean_inc_ref(v_a_6224_);
                lean_inc_ref(v_e_6217_);
                v___x_6243_ =
                    lean_infer_type(v_e_6217_, v_a_6224_, v_a_6225_, v_a_6226_, v_a_6227_);
                if lean_obj_tag(v___x_6243_) == 0 {
                    v_a_6244_ = lean_ctor_get(v___x_6243_, 0);
                    lean_inc(v_a_6244_);
                    lean_dec_ref_known(v___x_6243_, 1);
                    v___x_6245_ =
                        l_Lean_Meta_isProp(v_a_6244_, v_a_6224_, v_a_6225_, v_a_6226_, v_a_6227_);
                    if lean_obj_tag(v___x_6245_) == 0 {
                        v_a_6246_ = lean_ctor_get(v___x_6245_, 0);
                        lean_inc(v_a_6246_);
                        lean_dec_ref_known(v___x_6245_, 1);
                        v___f_6247_ = lean_alloc_closure(
                            l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed
                                as *mut core::ffi::c_void,
                            9,
                            4,
                        );
                        lean_closure_set(v___f_6247_, 0, v_e_6217_);
                        lean_closure_set(v___f_6247_, 1, v_t_x3f_6216_);
                        lean_closure_set(v___f_6247_, 2, v_a_6246_);
                        lean_closure_set(v___f_6247_, 3, v_h_x3f_6215_);
                        v___x_6248_ = l_Lean_Meta_withExposedNames___redArg(
                            v___f_6247_,
                            v_a_6224_,
                            v_a_6225_,
                            v_a_6226_,
                            v_a_6227_,
                        );
                        if lean_obj_tag(v___x_6248_) == 0 {
                            v_a_6249_ = lean_ctor_get(v___x_6248_, 0);
                            lean_inc(v_a_6249_);
                            lean_dec_ref_known(v___x_6248_, 1);
                            if lean_obj_tag(v_checkState_x3f_6219_) == 1 {
                                v_fst_6250_ = lean_ctor_get(v_a_6249_, 0);
                                lean_inc(v_fst_6250_);
                                v_snd_6251_ = lean_ctor_get(v_a_6249_, 1);
                                lean_inc_n(v_snd_6251_, 2);
                                lean_dec(v_a_6249_);
                                v_val_6252_ = lean_ctor_get(v_checkState_x3f_6219_, 0);
                                lean_inc(v_val_6252_);
                                lean_dec_ref_known(v_checkState_x3f_6219_, 1);
                                v___x_6253_ = lean_box(0);
                                v___x_6254_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_6250_, v_snd_6251_, v_val_6252_, v___x_6253_, v_a_6220_, v_a_6221_, v_a_6222_, v_a_6223_, v_a_6224_, v_a_6225_, v_a_6226_, v_a_6227_);
                                if lean_obj_tag(v___x_6254_) == 0 {
                                    v_a_6255_ = lean_ctor_get(v___x_6254_, 0);
                                    lean_inc(v_a_6255_);
                                    lean_dec_ref_known(v___x_6254_, 1);
                                    if lean_obj_tag(v_a_6255_) == 1 {
                                        lean_dec(v_snd_6251_);
                                        v_val_6256_ = lean_ctor_get(v_a_6255_, 0);
                                        lean_inc(v_val_6256_);
                                        lean_dec_ref_known(v_a_6255_, 1);
                                        v_fst_6257_ = lean_ctor_get(v_val_6256_, 0);
                                        lean_inc(v_fst_6257_);
                                        v_snd_6258_ = lean_ctor_get(v_val_6256_, 1);
                                        lean_inc(v_snd_6258_);
                                        lean_dec(v_val_6256_);
                                        v_tac_6230_ = v_fst_6257_;
                                        v_msg_6231_ = v_snd_6258_;
                                        v___y_6232_ = v_a_6226_;
                                        v___y_6233_ = v_a_6227_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v_a_6255_);
                                        lean_dec(v_origSpan_x3f_6218_);
                                        lean_dec(v_ref_6214_);
                                        v___x_6259_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2);
                                        v___x_6260_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_6259_, v_snd_6251_);
                                        v___x_6261_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v___x_6260_, v_a_6220_, v_a_6221_, v_a_6222_, v_a_6223_, v_a_6224_, v_a_6225_, v_a_6226_, v_a_6227_);
                                        if lean_obj_tag(v___x_6261_) == 0 {
                                            v_isSharedCheck_6269_ =
                                                (!lean_is_exclusive(v___x_6261_)) as u8;
                                            if v_isSharedCheck_6269_ == 0 {
                                                v_unused_6270_ = lean_ctor_get(v___x_6261_, 0);
                                                lean_dec(v_unused_6270_);
                                                v___x_6263_ = v___x_6261_;
                                                v_isShared_6264_ = v_isSharedCheck_6269_;
                                                state = 2;
                                                continue;
                                            } else {
                                                lean_dec(v___x_6261_);
                                                v___x_6263_ = lean_box(0);
                                                v_isShared_6264_ = v_isSharedCheck_6269_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            return v___x_6261_;
                                        }
                                    }
                                } else {
                                    lean_dec(v_snd_6251_);
                                    lean_dec(v_origSpan_x3f_6218_);
                                    lean_dec(v_ref_6214_);
                                    v_a_6271_ = lean_ctor_get(v___x_6254_, 0);
                                    v_isSharedCheck_6278_ = (!lean_is_exclusive(v___x_6254_)) as u8;
                                    if v_isSharedCheck_6278_ == 0 {
                                        v___x_6273_ = v___x_6254_;
                                        v_isShared_6274_ = v_isSharedCheck_6278_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6271_);
                                        lean_dec(v___x_6254_);
                                        v___x_6273_ = lean_box(0);
                                        v_isShared_6274_ = v_isSharedCheck_6278_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_checkState_x3f_6219_);
                                v_fst_6279_ = lean_ctor_get(v_a_6249_, 0);
                                lean_inc(v_fst_6279_);
                                v_snd_6280_ = lean_ctor_get(v_a_6249_, 1);
                                lean_inc(v_snd_6280_);
                                lean_dec(v_a_6249_);
                                v_tac_6230_ = v_fst_6279_;
                                v_msg_6231_ = v_snd_6280_;
                                v___y_6232_ = v_a_6226_;
                                v___y_6233_ = v_a_6227_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_checkState_x3f_6219_);
                            lean_dec(v_origSpan_x3f_6218_);
                            lean_dec(v_ref_6214_);
                            v_a_6281_ = lean_ctor_get(v___x_6248_, 0);
                            v_isSharedCheck_6288_ = (!lean_is_exclusive(v___x_6248_)) as u8;
                            if v_isSharedCheck_6288_ == 0 {
                                v___x_6283_ = v___x_6248_;
                                v_isShared_6284_ = v_isSharedCheck_6288_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_6281_);
                                lean_dec(v___x_6248_);
                                v___x_6283_ = lean_box(0);
                                v_isShared_6284_ = v_isSharedCheck_6288_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_checkState_x3f_6219_);
                        lean_dec(v_origSpan_x3f_6218_);
                        lean_dec_ref(v_e_6217_);
                        lean_dec(v_t_x3f_6216_);
                        lean_dec(v_h_x3f_6215_);
                        lean_dec(v_ref_6214_);
                        v_a_6289_ = lean_ctor_get(v___x_6245_, 0);
                        v_isSharedCheck_6296_ = (!lean_is_exclusive(v___x_6245_)) as u8;
                        if v_isSharedCheck_6296_ == 0 {
                            v___x_6291_ = v___x_6245_;
                            v_isShared_6292_ = v_isSharedCheck_6296_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_6289_);
                            lean_dec(v___x_6245_);
                            v___x_6291_ = lean_box(0);
                            v_isShared_6292_ = v_isSharedCheck_6296_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_checkState_x3f_6219_);
                    lean_dec(v_origSpan_x3f_6218_);
                    lean_dec_ref(v_e_6217_);
                    lean_dec(v_t_x3f_6216_);
                    lean_dec(v_h_x3f_6215_);
                    lean_dec(v_ref_6214_);
                    v_a_6297_ = lean_ctor_get(v___x_6243_, 0);
                    v_isSharedCheck_6304_ = (!lean_is_exclusive(v___x_6243_)) as u8;
                    if v_isSharedCheck_6304_ == 0 {
                        v___x_6299_ = v___x_6243_;
                        v_isShared_6300_ = v_isSharedCheck_6304_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6297_);
                        lean_dec(v___x_6243_);
                        v___x_6299_ = lean_box(0);
                        v_isShared_6300_ = v_isSharedCheck_6304_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6234_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1;
                v___x_6235_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6235_, 0, v___x_6234_);
                lean_ctor_set(v___x_6235_, 1, v_tac_6230_);
                v___x_6236_ = lean_box(0);
                v___x_6237_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6237_, 0, v_msg_6231_);
                v___x_6238_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_6238_, 0, v___x_6235_);
                lean_ctor_set(v___x_6238_, 1, v___x_6236_);
                lean_ctor_set(v___x_6238_, 2, v___x_6236_);
                lean_ctor_set(v___x_6238_, 3, v___x_6236_);
                lean_ctor_set(v___x_6238_, 4, v___x_6237_);
                lean_ctor_set(v___x_6238_, 5, v___x_6236_);
                v___x_6239_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0;
                v___x_6240_ = 4;
                v___x_6241_ = l_Lean_MessageData_nil;
                v___x_6242_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_ref_6214_,
                    v___x_6238_,
                    v_origSpan_x3f_6218_,
                    v___x_6239_,
                    v___x_6236_,
                    v___x_6240_,
                    v___x_6241_,
                    v___y_6232_,
                    v___y_6233_,
                );
                return v___x_6242_;
            }
            2 => {
                v___x_6265_ = lean_box(0);
                if v_isShared_6264_ == 0 {
                    lean_ctor_set(v___x_6263_, 0, v___x_6265_);
                    v___x_6267_ = v___x_6263_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6268_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6268_, 0, v___x_6265_);
                    v___x_6267_ = v_reuseFailAlloc_6268_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6267_;
            }
            4 => {
                if v_isShared_6274_ == 0 {
                    v___x_6276_ = v___x_6273_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6277_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6277_, 0, v_a_6271_);
                    v___x_6276_ = v_reuseFailAlloc_6277_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6276_;
            }
            6 => {
                if v_isShared_6284_ == 0 {
                    v___x_6286_ = v___x_6283_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6287_, 0, v_a_6281_);
                    v___x_6286_ = v_reuseFailAlloc_6287_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6286_;
            }
            8 => {
                if v_isShared_6292_ == 0 {
                    v___x_6294_ = v___x_6291_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6295_, 0, v_a_6289_);
                    v___x_6294_ = v_reuseFailAlloc_6295_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6294_;
            }
            10 => {
                if v_isShared_6300_ == 0 {
                    v___x_6302_ = v___x_6299_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6303_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6303_, 0, v_a_6297_);
                    v___x_6302_ = v_reuseFailAlloc_6303_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6302_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___boxed(
    mut v_ref_6305_: *mut LeanObject,
    mut v_h_x3f_6306_: *mut LeanObject,
    mut v_t_x3f_6307_: *mut LeanObject,
    mut v_e_6308_: *mut LeanObject,
    mut v_origSpan_x3f_6309_: *mut LeanObject,
    mut v_checkState_x3f_6310_: *mut LeanObject,
    mut v_a_6311_: *mut LeanObject,
    mut v_a_6312_: *mut LeanObject,
    mut v_a_6313_: *mut LeanObject,
    mut v_a_6314_: *mut LeanObject,
    mut v_a_6315_: *mut LeanObject,
    mut v_a_6316_: *mut LeanObject,
    mut v_a_6317_: *mut LeanObject,
    mut v_a_6318_: *mut LeanObject,
    mut v_a_6319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6320_: *mut LeanObject = core::ptr::null_mut();
    v_res_6320_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(
        v_ref_6305_,
        v_h_x3f_6306_,
        v_t_x3f_6307_,
        v_e_6308_,
        v_origSpan_x3f_6309_,
        v_checkState_x3f_6310_,
        v_a_6311_,
        v_a_6312_,
        v_a_6313_,
        v_a_6314_,
        v_a_6315_,
        v_a_6316_,
        v_a_6317_,
        v_a_6318_,
    );
    lean_dec(v_a_6318_);
    lean_dec_ref(v_a_6317_);
    lean_dec(v_a_6316_);
    lean_dec_ref(v_a_6315_);
    lean_dec(v_a_6314_);
    lean_dec_ref(v_a_6313_);
    lean_dec(v_a_6312_);
    lean_dec_ref(v_a_6311_);
    return v_res_6320_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(
    mut v_a_6322_: *mut LeanObject,
    mut v_a_6323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6329_: u8 = 0;
    let mut v___y_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6340_: u8 = 0;
    let mut v___y_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: u8 = 0;
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: u8 = 0;
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6357_: u8 = 0;
    let mut v_isSharedCheck_6358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6322_) == 0 {
                    v___x_6324_ = l_List_reverse___redArg(v_a_6323_);
                    return v___x_6324_;
                } else {
                    v_head_6325_ = lean_ctor_get(v_a_6322_, 0);
                    v_tail_6326_ = lean_ctor_get(v_a_6322_, 1);
                    v_isSharedCheck_6358_ = (!lean_is_exclusive(v_a_6322_)) as u8;
                    if v_isSharedCheck_6358_ == 0 {
                        v___x_6328_ = v_a_6322_;
                        v_isShared_6329_ = v_isSharedCheck_6358_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6326_);
                        lean_inc(v_head_6325_);
                        lean_dec(v_a_6322_);
                        v___x_6328_ = lean_box(0);
                        v_isShared_6329_ = v_isSharedCheck_6358_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6336_ = lean_ctor_get(v_head_6325_, 0);
                v_snd_6337_ = lean_ctor_get(v_head_6325_, 1);
                v_isSharedCheck_6357_ = (!lean_is_exclusive(v_head_6325_)) as u8;
                if v_isSharedCheck_6357_ == 0 {
                    v___x_6339_ = v_head_6325_;
                    v_isShared_6340_ = v_isSharedCheck_6357_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_6337_);
                    lean_inc(v_fst_6336_);
                    lean_dec(v_head_6325_);
                    v___x_6339_ = lean_box(0);
                    v_isShared_6340_ = v_isSharedCheck_6357_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_6329_ == 0 {
                    lean_ctor_set(v___x_6328_, 1, v_a_6323_);
                    lean_ctor_set(v___x_6328_, 0, v___y_6331_);
                    v___x_6333_ = v___x_6328_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6335_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6335_, 0, v___y_6331_);
                    lean_ctor_set(v_reuseFailAlloc_6335_, 1, v_a_6323_);
                    v___x_6333_ = v_reuseFailAlloc_6335_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_6322_ = v_tail_6326_;
                v_a_6323_ = v___x_6333_;
                state = 0;
                continue;
            }
            4 => {
                v___x_6354_ = (lean_unbox(v_snd_6337_) as u8);
                lean_dec(v_snd_6337_);
                if v___x_6354_ == 0 {
                    v___x_6355_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0;
                    v___y_6342_ = v___x_6355_;
                    state = 5;
                    continue;
                } else {
                    v___x_6356_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1___closed__0;
                    v___y_6342_ = v___x_6356_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v___y_6342_);
                v___x_6343_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6343_, 0, v___y_6342_);
                v___x_6344_ = l_Lean_MessageData_ofFormat(v___x_6343_);
                v___x_6345_ = l_Lean_Expr_isConst(v_fst_6336_);
                if v___x_6345_ == 0 {
                    v___x_6346_ = l_Lean_MessageData_ofExpr(v_fst_6336_);
                    if v_isShared_6340_ == 0 {
                        lean_ctor_set_tag(v___x_6339_, 7);
                        lean_ctor_set(v___x_6339_, 1, v___x_6346_);
                        lean_ctor_set(v___x_6339_, 0, v___x_6344_);
                        v___x_6348_ = v___x_6339_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6349_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6349_, 0, v___x_6344_);
                        lean_ctor_set(v_reuseFailAlloc_6349_, 1, v___x_6346_);
                        v___x_6348_ = v_reuseFailAlloc_6349_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_6350_ = l_Lean_MessageData_ofConst(v_fst_6336_);
                    if v_isShared_6340_ == 0 {
                        lean_ctor_set_tag(v___x_6339_, 7);
                        lean_ctor_set(v___x_6339_, 1, v___x_6350_);
                        lean_ctor_set(v___x_6339_, 0, v___x_6344_);
                        v___x_6352_ = v___x_6339_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6353_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6353_, 0, v___x_6344_);
                        lean_ctor_set(v_reuseFailAlloc_6353_, 1, v___x_6350_);
                        v___x_6352_ = v_reuseFailAlloc_6353_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v___y_6331_ = v___x_6348_;
                state = 2;
                continue;
            }
            7 => {
                v___y_6331_ = v___x_6352_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(
    mut v_sz_6366_: usize,
    mut v_i_6367_: usize,
    mut v_bs_6368_: *mut LeanObject,
    mut v___y_6369_: *mut LeanObject,
    mut v___y_6370_: *mut LeanObject,
    mut v___y_6371_: *mut LeanObject,
    mut v___y_6372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6374_: u8 = 0;
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6381_: u8 = 0;
    let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: usize = 0;
    let mut v___x_6387_: usize = 0;
    let mut v___x_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: u8 = 0;
    let mut v_a_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: u8 = 0;
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: u8 = 0;
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6417_: u8 = 0;
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6421_: u8 = 0;
    let mut v_isSharedCheck_6422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6374_ = lean_usize_dec_lt(v_i_6367_, v_sz_6366_);
                if v___x_6374_ == 0 {
                    v___x_6375_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6375_, 0, v_bs_6368_);
                    return v___x_6375_;
                } else {
                    v_v_6376_ = lean_array_uget(v_bs_6368_, v_i_6367_);
                    v_fst_6377_ = lean_ctor_get(v_v_6376_, 0);
                    v_snd_6378_ = lean_ctor_get(v_v_6376_, 1);
                    v_isSharedCheck_6422_ = (!lean_is_exclusive(v_v_6376_)) as u8;
                    if v_isSharedCheck_6422_ == 0 {
                        v___x_6380_ = v_v_6376_;
                        v_isShared_6381_ = v_isSharedCheck_6422_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6378_);
                        lean_inc(v_fst_6377_);
                        lean_dec(v_v_6376_);
                        v___x_6380_ = lean_box(0);
                        v_isShared_6381_ = v_isSharedCheck_6422_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6382_ = lean_unsigned_to_nat(0);
                v_bs_x27_6383_ = lean_array_uset(v_bs_6368_, v_i_6367_, v___x_6382_);
                v___x_6390_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(
                    v_fst_6377_,
                    v___y_6369_,
                    v___y_6370_,
                    v___y_6371_,
                    v___y_6372_,
                );
                if lean_obj_tag(v___x_6390_) == 0 {
                    v___x_6391_ = (lean_unbox(v_snd_6378_) as u8);
                    if v___x_6391_ == 0 {
                        lean_del_object(v___x_6380_);
                        v_a_6392_ = lean_ctor_get(v___x_6390_, 0);
                        lean_inc(v_a_6392_);
                        lean_dec_ref_known(v___x_6390_, 1);
                        v_ref_6393_ = lean_ctor_get(v___y_6371_, 5);
                        v___x_6394_ = (lean_unbox(v_snd_6378_) as u8);
                        lean_dec(v_snd_6378_);
                        v___x_6395_ = l_Lean_SourceInfo_fromRef(v_ref_6393_, v___x_6394_);
                        v___x_6396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1;
                        v___x_6397_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
                        v___x_6398_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once), _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
                        lean_inc(v___x_6395_);
                        v___x_6399_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_6399_, 0, v___x_6395_);
                        lean_ctor_set(v___x_6399_, 1, v___x_6397_);
                        lean_ctor_set(v___x_6399_, 2, v___x_6398_);
                        v___x_6400_ =
                            l_Lean_Syntax_node2(v___x_6395_, v___x_6396_, v___x_6399_, v_a_6392_);
                        v_a_6385_ = v___x_6400_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_snd_6378_);
                        v_a_6401_ = lean_ctor_get(v___x_6390_, 0);
                        lean_inc(v_a_6401_);
                        lean_dec_ref_known(v___x_6390_, 1);
                        v_ref_6402_ = lean_ctor_get(v___y_6371_, 5);
                        v___x_6403_ = 0;
                        v___x_6404_ = l_Lean_SourceInfo_fromRef(v_ref_6402_, v___x_6403_);
                        v___x_6405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1;
                        v___x_6406_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
                        v___x_6407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__2;
                        lean_inc(v___x_6404_);
                        if v_isShared_6381_ == 0 {
                            lean_ctor_set_tag(v___x_6380_, 2);
                            lean_ctor_set(v___x_6380_, 1, v___x_6407_);
                            lean_ctor_set(v___x_6380_, 0, v___x_6404_);
                            v___x_6409_ = v___x_6380_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6412_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6412_, 0, v___x_6404_);
                            lean_ctor_set(v_reuseFailAlloc_6412_, 1, v___x_6407_);
                            v___x_6409_ = v_reuseFailAlloc_6412_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_6380_);
                    lean_dec(v_snd_6378_);
                    if lean_obj_tag(v___x_6390_) == 0 {
                        v_a_6413_ = lean_ctor_get(v___x_6390_, 0);
                        lean_inc(v_a_6413_);
                        lean_dec_ref_known(v___x_6390_, 1);
                        v_a_6385_ = v_a_6413_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_x27_6383_);
                        v_a_6414_ = lean_ctor_get(v___x_6390_, 0);
                        v_isSharedCheck_6421_ = (!lean_is_exclusive(v___x_6390_)) as u8;
                        if v_isSharedCheck_6421_ == 0 {
                            v___x_6416_ = v___x_6390_;
                            v_isShared_6417_ = v_isSharedCheck_6421_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_6414_);
                            lean_dec(v___x_6390_);
                            v___x_6416_ = lean_box(0);
                            v_isShared_6417_ = v_isSharedCheck_6421_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_6386_ = 1usize;
                v___x_6387_ = lean_usize_add(v_i_6367_, v___x_6386_);
                v___x_6388_ = lean_array_uset(v_bs_x27_6383_, v_i_6367_, v_a_6385_);
                v_i_6367_ = v___x_6387_;
                v_bs_6368_ = v___x_6388_;
                state = 0;
                continue;
            }
            3 => {
                lean_inc(v___x_6404_);
                v___x_6410_ = l_Lean_Syntax_node1(v___x_6404_, v___x_6406_, v___x_6409_);
                v___x_6411_ = l_Lean_Syntax_node2(v___x_6404_, v___x_6405_, v___x_6410_, v_a_6401_);
                v_a_6385_ = v___x_6411_;
                state = 2;
                continue;
            }
            4 => {
                if v_isShared_6417_ == 0 {
                    v___x_6419_ = v___x_6416_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6420_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6420_, 0, v_a_6414_);
                    v___x_6419_ = v_reuseFailAlloc_6420_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___boxed(
    mut v_sz_6423_: *mut LeanObject,
    mut v_i_6424_: *mut LeanObject,
    mut v_bs_6425_: *mut LeanObject,
    mut v___y_6426_: *mut LeanObject,
    mut v___y_6427_: *mut LeanObject,
    mut v___y_6428_: *mut LeanObject,
    mut v___y_6429_: *mut LeanObject,
    mut v___y_6430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6431_: usize = 0;
    let mut v_i_boxed_6432_: usize = 0;
    let mut v_res_6433_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6431_ = lean_unbox_usize(v_sz_6423_);
    lean_dec(v_sz_6423_);
    v_i_boxed_6432_ = lean_unbox_usize(v_i_6424_);
    lean_dec(v_i_6424_);
    v_res_6433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_boxed_6431_, v_i_boxed_6432_, v_bs_6425_, v___y_6426_, v___y_6427_, v___y_6428_, v___y_6429_);
    lean_dec(v___y_6429_);
    lean_dec_ref(v___y_6428_);
    lean_dec(v___y_6427_);
    lean_dec_ref(v___y_6426_);
    return v_res_6433_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    v___x_6435_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__0;
    v___x_6436_ = l_Lean_stringToMessageData(v___x_6435_);
    return v___x_6436_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    v___x_6438_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__2;
    v___x_6439_ = l_Lean_stringToMessageData(v___x_6438_);
    return v___x_6439_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut LeanObject = core::ptr::null_mut();
    v___x_6440_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0;
    v___x_6441_ = l_Lean_stringToMessageData(v___x_6440_);
    return v___x_6441_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
    v___x_6445_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__6;
    v___x_6446_ = l_Lean_MessageData_ofFormat(v___x_6445_);
    return v___x_6446_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9()
-> *mut LeanObject {
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
    v___x_6448_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__8;
    v___x_6449_ = l_Lean_stringToMessageData(v___x_6448_);
    return v___x_6449_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11()
-> *mut LeanObject {
    let mut v___x_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut LeanObject = core::ptr::null_mut();
    v___x_6451_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__10;
    v___x_6452_ = l_Lean_stringToMessageData(v___x_6451_);
    return v___x_6452_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(
    mut v___x_6490_: *mut LeanObject,
    mut v_type_x3f_6491_: *mut LeanObject,
    mut v_rules_6492_: *mut LeanObject,
    mut v_loc_x3f_6493_: *mut LeanObject,
    mut v___y_6494_: *mut LeanObject,
    mut v___y_6495_: *mut LeanObject,
    mut v___y_6496_: *mut LeanObject,
    mut v___y_6497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraMsg_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6547_: usize = 0;
    let mut v___x_6548_: usize = 0;
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: u8 = 0;
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: u8 = 0;
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6601_: u8 = 0;
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6605_: u8 = 0;
    let mut v_a_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6609_: u8 = 0;
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_6547_ = lean_array_size(v___x_6490_);
                v___x_6548_ = 0usize;
                v___x_6549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_6547_, v___x_6548_, v___x_6490_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_);
                if lean_obj_tag(v___x_6549_) == 0 {
                    v_a_6550_ = lean_ctor_get(v___x_6549_, 0);
                    lean_inc(v_a_6550_);
                    lean_dec_ref_known(v___x_6549_, 1);
                    v___x_6551_ =
                        l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__12;
                    v___x_6552_ = l_Lean_Syntax_SepArray_ofElems(v___x_6551_, v_a_6550_);
                    lean_dec(v_a_6550_);
                    if lean_obj_tag(v_loc_x3f_6493_) == 0 {
                        v___x_6581_ = lean_box(0);
                        v_a_6554_ = v___x_6581_;
                        state = 4;
                        continue;
                    } else {
                        v_val_6582_ = lean_ctor_get(v_loc_x3f_6493_, 0);
                        v___x_6583_ = lean_box(1);
                        lean_inc(v_val_6582_);
                        v___x_6584_ = l_Lean_PrettyPrinter_delab(
                            v_val_6582_,
                            v___x_6583_,
                            v___y_6494_,
                            v___y_6495_,
                            v___y_6496_,
                            v___y_6497_,
                        );
                        if lean_obj_tag(v___x_6584_) == 0 {
                            v_a_6585_ = lean_ctor_get(v___x_6584_, 0);
                            lean_inc(v_a_6585_);
                            lean_dec_ref_known(v___x_6584_, 1);
                            v_ref_6586_ = lean_ctor_get(v___y_6496_, 5);
                            v___x_6587_ = 0;
                            v___x_6588_ = l_Lean_SourceInfo_fromRef(v_ref_6586_, v___x_6587_);
                            v___x_6589_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24;
                            v___x_6590_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__25;
                            lean_inc_n(v___x_6588_, 3);
                            v___x_6591_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_6591_, 0, v___x_6588_);
                            lean_ctor_set(v___x_6591_, 1, v___x_6590_);
                            v___x_6592_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27;
                            v___x_6593_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
                            v___x_6594_ = l_Lean_Syntax_node1(v___x_6588_, v___x_6593_, v_a_6585_);
                            v___x_6595_ =
                                l_Lean_Syntax_node1(v___x_6588_, v___x_6592_, v___x_6594_);
                            v___x_6596_ = l_Lean_Syntax_node2(
                                v___x_6588_,
                                v___x_6589_,
                                v___x_6591_,
                                v___x_6595_,
                            );
                            v_a_6579_ = v___x_6596_;
                            state = 5;
                            continue;
                        } else {
                            if lean_obj_tag(v___x_6584_) == 0 {
                                v_a_6597_ = lean_ctor_get(v___x_6584_, 0);
                                lean_inc(v_a_6597_);
                                lean_dec_ref_known(v___x_6584_, 1);
                                v_a_6579_ = v_a_6597_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec_ref_known(v_loc_x3f_6493_, 1);
                                lean_dec_ref(v___x_6552_);
                                lean_dec(v_rules_6492_);
                                lean_dec(v_type_x3f_6491_);
                                v_a_6598_ = lean_ctor_get(v___x_6584_, 0);
                                v_isSharedCheck_6605_ = (!lean_is_exclusive(v___x_6584_)) as u8;
                                if v_isSharedCheck_6605_ == 0 {
                                    v___x_6600_ = v___x_6584_;
                                    v_isShared_6601_ = v_isSharedCheck_6605_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_6598_);
                                    lean_dec(v___x_6584_);
                                    v___x_6600_ = lean_box(0);
                                    v_isShared_6601_ = v_isSharedCheck_6605_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v_loc_x3f_6493_);
                    lean_dec(v_rules_6492_);
                    lean_dec(v_type_x3f_6491_);
                    v_a_6606_ = lean_ctor_get(v___x_6549_, 0);
                    v_isSharedCheck_6613_ = (!lean_is_exclusive(v___x_6549_)) as u8;
                    if v_isSharedCheck_6613_ == 0 {
                        v___x_6608_ = v___x_6549_;
                        v_isShared_6609_ = v_isSharedCheck_6613_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6606_);
                        lean_dec(v___x_6549_);
                        v___x_6608_ = lean_box(0);
                        v_isShared_6609_ = v_isSharedCheck_6613_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6503_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6503_, 0, v___y_6501_);
                lean_ctor_set(v___x_6503_, 1, v_extraMsg_6502_);
                v___x_6504_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6504_, 0, v___y_6500_);
                lean_ctor_set(v___x_6504_, 1, v___x_6503_);
                v___x_6505_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6505_, 0, v___x_6504_);
                return v___x_6505_;
            }
            2 => {
                v___x_6509_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___y_6508_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_);
                match lean_obj_tag(v_type_x3f_6491_) {
                    0 => {
                        v_a_6510_ = lean_ctor_get(v___x_6509_, 0);
                        lean_inc(v_a_6510_);
                        lean_dec_ref(v___x_6509_);
                        v___x_6511_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1_once), _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1);
                        v___y_6500_ = v___y_6507_;
                        v___y_6501_ = v_a_6510_;
                        v_extraMsg_6502_ = v___x_6511_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v_a_6512_ = lean_ctor_get(v___x_6509_, 0);
                        lean_inc(v_a_6512_);
                        lean_dec_ref(v___x_6509_);
                        v_a_6513_ = lean_ctor_get(v_type_x3f_6491_, 0);
                        lean_inc(v_a_6513_);
                        lean_dec_ref_known(v_type_x3f_6491_, 1);
                        v___x_6514_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3_once), _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3);
                        v___x_6515_ = l_Lean_MessageData_ofExpr(v_a_6513_);
                        v___x_6516_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6516_, 0, v___x_6514_);
                        lean_ctor_set(v___x_6516_, 1, v___x_6515_);
                        v___x_6517_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_6516_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_);
                        v_a_6518_ = lean_ctor_get(v___x_6517_, 0);
                        lean_inc(v_a_6518_);
                        lean_dec_ref(v___x_6517_);
                        v___y_6500_ = v___y_6507_;
                        v___y_6501_ = v_a_6512_;
                        v_extraMsg_6502_ = v_a_6518_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v_a_6519_ = lean_ctor_get(v___x_6509_, 0);
                        lean_inc(v_a_6519_);
                        lean_dec_ref(v___x_6509_);
                        v___x_6520_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4_once), _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4);
                        v___y_6500_ = v___y_6507_;
                        v___y_6501_ = v_a_6519_;
                        v_extraMsg_6502_ = v___x_6520_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6530_ = l_Array_append___redArg(v___y_6525_, v___y_6529_);
                lean_dec_ref(v___y_6529_);
                lean_inc(v___y_6527_);
                lean_inc(v___y_6524_);
                v___x_6531_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6531_, 0, v___y_6524_);
                lean_ctor_set(v___x_6531_, 1, v___y_6527_);
                lean_ctor_set(v___x_6531_, 2, v___x_6530_);
                lean_inc(v___y_6528_);
                v___x_6532_ = l_Lean_Syntax_node4(
                    v___y_6524_,
                    v___y_6528_,
                    v___y_6526_,
                    v___y_6522_,
                    v___y_6523_,
                    v___x_6531_,
                );
                v___x_6533_ = lean_box(0);
                v___x_6534_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(v_rules_6492_, v___x_6533_);
                v___x_6535_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7,
                );
                v___x_6536_ = l_Lean_MessageData_joinSep(v___x_6534_, v___x_6535_);
                v___x_6537_ = l_Lean_MessageData_sbracket(v___x_6536_);
                if lean_obj_tag(v_loc_x3f_6493_) == 1 {
                    v_val_6538_ = lean_ctor_get(v_loc_x3f_6493_, 0);
                    lean_inc(v_val_6538_);
                    lean_dec_ref_known(v_loc_x3f_6493_, 1);
                    v___x_6539_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once), _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9);
                    v___x_6540_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6540_, 0, v___x_6539_);
                    lean_ctor_set(v___x_6540_, 1, v___x_6537_);
                    v___x_6541_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11_once), _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11);
                    v___x_6542_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6542_, 0, v___x_6540_);
                    lean_ctor_set(v___x_6542_, 1, v___x_6541_);
                    v___x_6543_ = l_Lean_MessageData_ofExpr(v_val_6538_);
                    v___x_6544_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6544_, 0, v___x_6542_);
                    lean_ctor_set(v___x_6544_, 1, v___x_6543_);
                    v___y_6507_ = v___x_6532_;
                    v___y_6508_ = v___x_6544_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_loc_x3f_6493_);
                    v___x_6545_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once), _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9);
                    v___x_6546_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6546_, 0, v___x_6545_);
                    lean_ctor_set(v___x_6546_, 1, v___x_6537_);
                    v___y_6507_ = v___x_6532_;
                    v___y_6508_ = v___x_6546_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_ref_6555_ = lean_ctor_get(v___y_6496_, 5);
                v___x_6556_ = 0;
                v___x_6557_ = l_Lean_SourceInfo_fromRef(v_ref_6555_, v___x_6556_);
                v___x_6558_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14;
                v___x_6559_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__15;
                lean_inc_n(v___x_6557_, 7);
                v___x_6560_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6560_, 0, v___x_6557_);
                lean_ctor_set(v___x_6560_, 1, v___x_6559_);
                v___x_6561_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17;
                v___x_6562_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
                v___x_6563_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6,
                );
                v___x_6564_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6564_, 0, v___x_6557_);
                lean_ctor_set(v___x_6564_, 1, v___x_6562_);
                lean_ctor_set(v___x_6564_, 2, v___x_6563_);
                v___x_6565_ = l_Lean_Syntax_node1(v___x_6557_, v___x_6561_, v___x_6564_);
                v___x_6566_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19;
                v___x_6567_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__20;
                v___x_6568_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6568_, 0, v___x_6557_);
                lean_ctor_set(v___x_6568_, 1, v___x_6567_);
                v___x_6569_ = l_Array_append___redArg(v___x_6563_, v___x_6552_);
                lean_dec_ref(v___x_6552_);
                v___x_6570_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6570_, 0, v___x_6557_);
                lean_ctor_set(v___x_6570_, 1, v___x_6562_);
                lean_ctor_set(v___x_6570_, 2, v___x_6569_);
                v___x_6571_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__21;
                v___x_6572_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6572_, 0, v___x_6557_);
                lean_ctor_set(v___x_6572_, 1, v___x_6571_);
                v___x_6573_ = l_Lean_Syntax_node3(
                    v___x_6557_,
                    v___x_6566_,
                    v___x_6568_,
                    v___x_6570_,
                    v___x_6572_,
                );
                if lean_obj_tag(v_a_6554_) == 0 {
                    v___x_6574_ =
                        l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22;
                    v___y_6522_ = v___x_6565_;
                    v___y_6523_ = v___x_6573_;
                    v___y_6524_ = v___x_6557_;
                    v___y_6525_ = v___x_6563_;
                    v___y_6526_ = v___x_6560_;
                    v___y_6527_ = v___x_6562_;
                    v___y_6528_ = v___x_6558_;
                    v___y_6529_ = v___x_6574_;
                    state = 3;
                    continue;
                } else {
                    v_val_6575_ = lean_ctor_get(v_a_6554_, 0);
                    lean_inc(v_val_6575_);
                    lean_dec_ref_known(v_a_6554_, 1);
                    v___x_6576_ =
                        l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22;
                    v___x_6577_ = lean_array_push(v___x_6576_, v_val_6575_);
                    v___y_6522_ = v___x_6565_;
                    v___y_6523_ = v___x_6573_;
                    v___y_6524_ = v___x_6557_;
                    v___y_6525_ = v___x_6563_;
                    v___y_6526_ = v___x_6560_;
                    v___y_6527_ = v___x_6562_;
                    v___y_6528_ = v___x_6558_;
                    v___y_6529_ = v___x_6577_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_6580_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6580_, 0, v_a_6579_);
                v_a_6554_ = v___x_6580_;
                state = 4;
                continue;
            }
            6 => {
                if v_isShared_6601_ == 0 {
                    v___x_6603_ = v___x_6600_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6604_, 0, v_a_6598_);
                    v___x_6603_ = v_reuseFailAlloc_6604_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6603_;
            }
            8 => {
                if v_isShared_6609_ == 0 {
                    v___x_6611_ = v___x_6608_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6612_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6612_, 0, v_a_6606_);
                    v___x_6611_ = v_reuseFailAlloc_6612_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed(
    mut v___x_6614_: *mut LeanObject,
    mut v_type_x3f_6615_: *mut LeanObject,
    mut v_rules_6616_: *mut LeanObject,
    mut v_loc_x3f_6617_: *mut LeanObject,
    mut v___y_6618_: *mut LeanObject,
    mut v___y_6619_: *mut LeanObject,
    mut v___y_6620_: *mut LeanObject,
    mut v___y_6621_: *mut LeanObject,
    mut v___y_6622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6623_: *mut LeanObject = core::ptr::null_mut();
    v_res_6623_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(
        v___x_6614_,
        v_type_x3f_6615_,
        v_rules_6616_,
        v_loc_x3f_6617_,
        v___y_6618_,
        v___y_6619_,
        v___y_6620_,
        v___y_6621_,
    );
    lean_dec(v___y_6621_);
    lean_dec_ref(v___y_6620_);
    lean_dec(v___y_6619_);
    lean_dec_ref(v___y_6618_);
    return v_res_6623_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2() -> *mut LeanObject
{
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut LeanObject = core::ptr::null_mut();
    v___x_6627_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1;
    v___x_6628_ = l_Lean_MessageData_ofFormat(v___x_6627_);
    return v___x_6628_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(
    mut v_ref_6629_: *mut LeanObject,
    mut v_rules_6630_: *mut LeanObject,
    mut v_type_x3f_6631_: *mut LeanObject,
    mut v_loc_x3f_6632_: *mut LeanObject,
    mut v_origSpan_x3f_6633_: *mut LeanObject,
    mut v_checkState_x3f_6634_: *mut LeanObject,
    mut v_a_6635_: *mut LeanObject,
    mut v_a_6636_: *mut LeanObject,
    mut v_a_6637_: *mut LeanObject,
    mut v_a_6638_: *mut LeanObject,
    mut v_a_6639_: *mut LeanObject,
    mut v_a_6640_: *mut LeanObject,
    mut v_a_6641_: *mut LeanObject,
    mut v_a_6642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6652_: u8 = 0;
    let mut v_fst_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6657_: u8 = 0;
    let mut v_tac_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tacMsg_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: u8 = 0;
    let mut v___x_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6680_: u8 = 0;
    let mut v___y_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6698_: u8 = 0;
    let mut v___x_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6703_: u8 = 0;
    let mut v_unused_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6708_: u8 = 0;
    let mut v___x_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6712_: u8 = 0;
    let mut v_a_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6718_: u8 = 0;
    let mut v_isSharedCheck_6719_: u8 = 0;
    let mut v_isSharedCheck_6720_: u8 = 0;
    let mut v_a_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6724_: u8 = 0;
    let mut v___x_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6728_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_rules_6630_);
                v___x_6644_ = lean_array_mk(v_rules_6630_);
                lean_inc(v_type_x3f_6631_);
                v___f_6645_ = lean_alloc_closure(
                    l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed
                        as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___f_6645_, 0, v___x_6644_);
                lean_closure_set(v___f_6645_, 1, v_type_x3f_6631_);
                lean_closure_set(v___f_6645_, 2, v_rules_6630_);
                lean_closure_set(v___f_6645_, 3, v_loc_x3f_6632_);
                v___x_6646_ = l_Lean_Meta_withExposedNames___redArg(
                    v___f_6645_,
                    v_a_6639_,
                    v_a_6640_,
                    v_a_6641_,
                    v_a_6642_,
                );
                if lean_obj_tag(v___x_6646_) == 0 {
                    v_a_6647_ = lean_ctor_get(v___x_6646_, 0);
                    lean_inc(v_a_6647_);
                    lean_dec_ref_known(v___x_6646_, 1);
                    v_snd_6648_ = lean_ctor_get(v_a_6647_, 1);
                    v_fst_6649_ = lean_ctor_get(v_a_6647_, 0);
                    v_isSharedCheck_6720_ = (!lean_is_exclusive(v_a_6647_)) as u8;
                    if v_isSharedCheck_6720_ == 0 {
                        v___x_6651_ = v_a_6647_;
                        v_isShared_6652_ = v_isSharedCheck_6720_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6648_);
                        lean_inc(v_fst_6649_);
                        lean_dec(v_a_6647_);
                        v___x_6651_ = lean_box(0);
                        v_isShared_6652_ = v_isSharedCheck_6720_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_checkState_x3f_6634_);
                    lean_dec(v_origSpan_x3f_6633_);
                    lean_dec(v_type_x3f_6631_);
                    lean_dec(v_ref_6629_);
                    v_a_6721_ = lean_ctor_get(v___x_6646_, 0);
                    v_isSharedCheck_6728_ = (!lean_is_exclusive(v___x_6646_)) as u8;
                    if v_isSharedCheck_6728_ == 0 {
                        v___x_6723_ = v___x_6646_;
                        v_isShared_6724_ = v_isSharedCheck_6728_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_6721_);
                        lean_dec(v___x_6646_);
                        v___x_6723_ = lean_box(0);
                        v_isShared_6724_ = v_isSharedCheck_6728_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6653_ = lean_ctor_get(v_snd_6648_, 0);
                v_snd_6654_ = lean_ctor_get(v_snd_6648_, 1);
                v_isSharedCheck_6719_ = (!lean_is_exclusive(v_snd_6648_)) as u8;
                if v_isSharedCheck_6719_ == 0 {
                    v___x_6656_ = v_snd_6648_;
                    v_isShared_6657_ = v_isSharedCheck_6719_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_6654_);
                    lean_inc(v_fst_6653_);
                    lean_dec(v_snd_6648_);
                    v___x_6656_ = lean_box(0);
                    v_isShared_6657_ = v_isSharedCheck_6719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if lean_obj_tag(v_checkState_x3f_6634_) == 1 {
                    v_val_6677_ = lean_ctor_get(v_checkState_x3f_6634_, 0);
                    v_isSharedCheck_6718_ = (!lean_is_exclusive(v_checkState_x3f_6634_)) as u8;
                    if v_isSharedCheck_6718_ == 0 {
                        v___x_6679_ = v_checkState_x3f_6634_;
                        v_isShared_6680_ = v_isSharedCheck_6718_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_val_6677_);
                        lean_dec(v_checkState_x3f_6634_);
                        v___x_6679_ = lean_box(0);
                        v_isShared_6680_ = v_isSharedCheck_6718_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_checkState_x3f_6634_);
                    lean_dec(v_type_x3f_6631_);
                    v_tac_6659_ = v_fst_6649_;
                    v_tacMsg_6660_ = v_fst_6653_;
                    v___y_6661_ = v_a_6641_;
                    v___y_6662_ = v_a_6642_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6663_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1;
                if v_isShared_6657_ == 0 {
                    lean_ctor_set(v___x_6656_, 1, v_tac_6659_);
                    lean_ctor_set(v___x_6656_, 0, v___x_6663_);
                    v___x_6665_ = v___x_6656_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6676_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6676_, 0, v___x_6663_);
                    lean_ctor_set(v_reuseFailAlloc_6676_, 1, v_tac_6659_);
                    v___x_6665_ = v_reuseFailAlloc_6676_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6666_ = lean_box(0);
                if v_isShared_6652_ == 0 {
                    lean_ctor_set_tag(v___x_6651_, 7);
                    lean_ctor_set(v___x_6651_, 1, v_snd_6654_);
                    lean_ctor_set(v___x_6651_, 0, v_tacMsg_6660_);
                    v___x_6668_ = v___x_6651_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6675_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6675_, 0, v_tacMsg_6660_);
                    lean_ctor_set(v_reuseFailAlloc_6675_, 1, v_snd_6654_);
                    v___x_6668_ = v_reuseFailAlloc_6675_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6669_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6669_, 0, v___x_6668_);
                v___x_6670_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_6670_, 0, v___x_6665_);
                lean_ctor_set(v___x_6670_, 1, v___x_6666_);
                lean_ctor_set(v___x_6670_, 2, v___x_6666_);
                lean_ctor_set(v___x_6670_, 3, v___x_6666_);
                lean_ctor_set(v___x_6670_, 4, v___x_6669_);
                lean_ctor_set(v___x_6670_, 5, v___x_6666_);
                v___x_6671_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0;
                v___x_6672_ = 4;
                v___x_6673_ = l_Lean_MessageData_nil;
                v___x_6674_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_ref_6629_,
                    v___x_6670_,
                    v_origSpan_x3f_6633_,
                    v___x_6671_,
                    v___x_6666_,
                    v___x_6672_,
                    v___x_6673_,
                    v___y_6661_,
                    v___y_6662_,
                );
                return v___x_6674_;
            }
            6 => {
                if lean_obj_tag(v_type_x3f_6631_) == 1 {
                    v_a_6713_ = lean_ctor_get(v_type_x3f_6631_, 0);
                    lean_inc(v_a_6713_);
                    lean_dec_ref_known(v_type_x3f_6631_, 1);
                    if v_isShared_6680_ == 0 {
                        lean_ctor_set(v___x_6679_, 0, v_a_6713_);
                        v___x_6715_ = v___x_6679_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_6716_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6716_, 0, v_a_6713_);
                        v___x_6715_ = v_reuseFailAlloc_6716_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6679_);
                    lean_dec(v_type_x3f_6631_);
                    v___x_6717_ = lean_box(0);
                    v___y_6682_ = v___x_6717_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_inc(v_fst_6653_);
                v___x_6683_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_6649_, v_fst_6653_, v_val_6677_, v___y_6682_, v_a_6635_, v_a_6636_, v_a_6637_, v_a_6638_, v_a_6639_, v_a_6640_, v_a_6641_, v_a_6642_);
                if lean_obj_tag(v___x_6683_) == 0 {
                    v_a_6684_ = lean_ctor_get(v___x_6683_, 0);
                    lean_inc(v_a_6684_);
                    lean_dec_ref_known(v___x_6683_, 1);
                    if lean_obj_tag(v_a_6684_) == 1 {
                        lean_dec(v_fst_6653_);
                        v_val_6685_ = lean_ctor_get(v_a_6684_, 0);
                        lean_inc(v_val_6685_);
                        lean_dec_ref_known(v_a_6684_, 1);
                        v_fst_6686_ = lean_ctor_get(v_val_6685_, 0);
                        lean_inc(v_fst_6686_);
                        v_snd_6687_ = lean_ctor_get(v_val_6685_, 1);
                        lean_inc(v_snd_6687_);
                        lean_dec(v_val_6685_);
                        v_tac_6659_ = v_fst_6686_;
                        v_tacMsg_6660_ = v_snd_6687_;
                        v___y_6661_ = v_a_6641_;
                        v___y_6662_ = v_a_6642_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_a_6684_);
                        lean_del_object(v___x_6656_);
                        lean_del_object(v___x_6651_);
                        lean_dec(v_origSpan_x3f_6633_);
                        lean_dec(v_ref_6629_);
                        v___x_6688_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
                        v___x_6689_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6689_, 0, v___x_6688_);
                        lean_ctor_set(v___x_6689_, 1, v_fst_6653_);
                        v___x_6690_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once), _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
                        v___x_6691_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6691_, 0, v___x_6689_);
                        lean_ctor_set(v___x_6691_, 1, v___x_6690_);
                        v___x_6692_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2_once
                            ),
                            _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2,
                        );
                        v___x_6693_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6693_, 0, v___x_6691_);
                        lean_ctor_set(v___x_6693_, 1, v_snd_6654_);
                        v___x_6694_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_6692_, v___x_6693_);
                        v___x_6695_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v___x_6694_, v_a_6635_, v_a_6636_, v_a_6637_, v_a_6638_, v_a_6639_, v_a_6640_, v_a_6641_, v_a_6642_);
                        if lean_obj_tag(v___x_6695_) == 0 {
                            v_isSharedCheck_6703_ = (!lean_is_exclusive(v___x_6695_)) as u8;
                            if v_isSharedCheck_6703_ == 0 {
                                v_unused_6704_ = lean_ctor_get(v___x_6695_, 0);
                                lean_dec(v_unused_6704_);
                                v___x_6697_ = v___x_6695_;
                                v_isShared_6698_ = v_isSharedCheck_6703_;
                                state = 8;
                                continue;
                            } else {
                                lean_dec(v___x_6695_);
                                v___x_6697_ = lean_box(0);
                                v_isShared_6698_ = v_isSharedCheck_6703_;
                                state = 8;
                                continue;
                            }
                        } else {
                            return v___x_6695_;
                        }
                    }
                } else {
                    lean_del_object(v___x_6656_);
                    lean_dec(v_snd_6654_);
                    lean_dec(v_fst_6653_);
                    lean_del_object(v___x_6651_);
                    lean_dec(v_origSpan_x3f_6633_);
                    lean_dec(v_ref_6629_);
                    v_a_6705_ = lean_ctor_get(v___x_6683_, 0);
                    v_isSharedCheck_6712_ = (!lean_is_exclusive(v___x_6683_)) as u8;
                    if v_isSharedCheck_6712_ == 0 {
                        v___x_6707_ = v___x_6683_;
                        v_isShared_6708_ = v_isSharedCheck_6712_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6705_);
                        lean_dec(v___x_6683_);
                        v___x_6707_ = lean_box(0);
                        v_isShared_6708_ = v_isSharedCheck_6712_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_6699_ = lean_box(0);
                if v_isShared_6698_ == 0 {
                    lean_ctor_set(v___x_6697_, 0, v___x_6699_);
                    v___x_6701_ = v___x_6697_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6702_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6702_, 0, v___x_6699_);
                    v___x_6701_ = v_reuseFailAlloc_6702_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6701_;
            }
            10 => {
                if v_isShared_6708_ == 0 {
                    v___x_6710_ = v___x_6707_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6711_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6711_, 0, v_a_6705_);
                    v___x_6710_ = v_reuseFailAlloc_6711_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6710_;
            }
            12 => {
                v___y_6682_ = v___x_6715_;
                state = 7;
                continue;
            }
            13 => {
                if v_isShared_6724_ == 0 {
                    v___x_6726_ = v___x_6723_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6727_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6727_, 0, v_a_6721_);
                    v___x_6726_ = v_reuseFailAlloc_6727_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed(
    mut v_ref_6729_: *mut LeanObject,
    mut v_rules_6730_: *mut LeanObject,
    mut v_type_x3f_6731_: *mut LeanObject,
    mut v_loc_x3f_6732_: *mut LeanObject,
    mut v_origSpan_x3f_6733_: *mut LeanObject,
    mut v_checkState_x3f_6734_: *mut LeanObject,
    mut v_a_6735_: *mut LeanObject,
    mut v_a_6736_: *mut LeanObject,
    mut v_a_6737_: *mut LeanObject,
    mut v_a_6738_: *mut LeanObject,
    mut v_a_6739_: *mut LeanObject,
    mut v_a_6740_: *mut LeanObject,
    mut v_a_6741_: *mut LeanObject,
    mut v_a_6742_: *mut LeanObject,
    mut v_a_6743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6744_: *mut LeanObject = core::ptr::null_mut();
    v_res_6744_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(
        v_ref_6729_,
        v_rules_6730_,
        v_type_x3f_6731_,
        v_loc_x3f_6732_,
        v_origSpan_x3f_6733_,
        v_checkState_x3f_6734_,
        v_a_6735_,
        v_a_6736_,
        v_a_6737_,
        v_a_6738_,
        v_a_6739_,
        v_a_6740_,
        v_a_6741_,
        v_a_6742_,
    );
    lean_dec(v_a_6742_);
    lean_dec_ref(v_a_6741_);
    lean_dec(v_a_6740_);
    lean_dec_ref(v_a_6739_);
    lean_dec(v_a_6738_);
    lean_dec_ref(v_a_6737_);
    lean_dec(v_a_6736_);
    lean_dec_ref(v_a_6735_);
    return v_res_6744_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_TryThis(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_CodeActions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_ExposeNames(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_UserWidget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_TryThis(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Widget_UserWidget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_TryThis(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_CodeActions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_ExposeNames(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Widget_UserWidget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_TryThis(builtin);
}
