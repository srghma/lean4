// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Lint
// Imports: Lean.Elab.Command Init.Grind.Lint Lean.Elab.Tactic.Grind.Config Lean.Meta.Tactic.TryThis
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Grind::Lint::{
    initialize_Init_Grind_Lint, runtime_initialize_Init_Grind_Lint,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getId};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_replaceRef, l_List_lengthTR___redArg, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::{
    l_Lean_Name_components, l_Lean_Name_isAnonymous, l_Lean_Name_isPrefixOf, l_Lean_Name_lt,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_liftTermElabM___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo;
use crate::r#gen::Lean::Elab::Tactic::Grind::Config::{
    initialize_Lean_Elab_Tactic_Grind_Config, l_Lean_Elab_Tactic_Grind_elabConfigItems___redArg,
    runtime_initialize_Lean_Elab_Tactic_Grind_Config,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData,
    l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_mvarId_x21, l_Lean_mkConst};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_nil,
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_mkFreshExprMVar,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Attr::l_Lean_Meta_Grind_grindExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchTheorem::{
    l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg,
    l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Extension::l_Lean_Meta_Grind_instInhabitedExtensionState_default;
use crate::r#gen::Lean::Meta::Tactic::Grind::Main::{
    l_Lean_Meta_Grind_main, l_Lean_Meta_Grind_mkDefaultParams,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Theorems::{
    l_Lean_Meta_Grind_Theorems_eraseDecl___redArg, l_Lean_Meta_Grind_Theorems_getOrigins___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::TryThis::{
    initialize_Lean_Meta_Tactic_TryThis, l_Lean_Meta_Tactic_TryThis_addSuggestion,
    runtime_initialize_Lean_Meta_Tactic_TryThis,
};
use crate::r#gen::Lean::PrettyPrinter::{
    l_Lean_MessageData_ofConst, l_Lean_PrettyPrinter_ppCategory,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq, lean_string_utf8_byte_size,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_NameSet_insert as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5409699204079762053 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4907018543776028915 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 110, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,725077744578949815 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,3195462025930095818 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17384550024581932235 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__16_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13754810025250588829 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__16_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__16_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__17_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__16_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8247902359227269508 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__17_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__17_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__17_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15821942484944040542 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 107, 105, 112, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13547010938738190075 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 107, 105, 112, 83, 117, 102, 102, 105, 120, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8061598928226805829 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 117, 116, 101, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16910188556949506335 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__2_value: crate::leanh::LeanStringObject<72> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 72, m_capacity: 72, m_length: 71, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 109, 97, 114, 107, 101, 100, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 96, 64, 91, 103, 114, 105, 110, 100, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 102, 111, 114, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [96, 32, 105, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 105, 110, 32, 116, 104, 101, 32, 96, 35, 103, 114, 105, 110, 100, 95, 108, 105, 110, 116, 96, 32, 115, 107, 105, 112, 32, 115, 101, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0_value: crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [96, 32, 105, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 105, 110, 32, 116, 104, 101, 32, 96, 35, 103, 114, 105, 110, 100, 95, 108, 105, 110, 116, 96, 32, 115, 107, 105, 112, 32, 115, 117, 102, 102, 105, 120, 32, 115, 101, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [103, 114, 105, 110, 100, 76, 105, 110, 116, 83, 107, 105, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__0_value) as *mut crate::leanh::LeanObject,949591075816843266 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__0_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 108, 97, 98, 71, 114, 105, 110, 100, 76, 105, 110, 116, 83, 107, 105, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__0_value) as *mut crate::leanh::LeanObject,8739318810695013922 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__0_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [96, 32, 105, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 105, 110, 32, 116, 104, 101, 32, 96, 35, 103, 114, 105, 110, 100, 95, 108, 105, 110, 116, 96, 32, 109, 117, 116, 101, 32, 115, 101, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [103, 114, 105, 110, 100, 76, 105, 110, 116, 77, 117, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__0_value) as *mut crate::leanh::LeanObject,543388241676410444 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed__const__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + core::mem::size_of::<usize>()*1) as u16, other: 1, tag: 0 }, m_objs: [(0 as *mut crate::leanh::LeanObject)] };
pub static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed__const__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__0_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 108, 97, 98, 71, 114, 105, 110, 100, 76, 105, 110, 116, 77, 117, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__0_value) as *mut crate::leanh::LeanObject,14853236627299621360 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0_value: crate::leanh::LeanCtorObject<17> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*13 + 32) as u16, other: 13, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 10 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 8 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 100 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 1000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 100000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 1000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 1048576 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 10 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,72340168526266368 as *mut crate::leanh::LeanObject,72058697844588544 as *mut crate::leanh::LeanObject,72340172838010881 as *mut crate::leanh::LeanObject,72339073326448897 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 104, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11262269099723811472 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2: f64 = 0.0;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [32, 226, 134, 166, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__6_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,907667957179513571 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,8738205681931236784 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__1_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__3_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__4_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__1_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__4_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 105, 110, 103, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [96, 32, 116, 114, 105, 103, 103, 101, 114, 115, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__8_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [32, 97, 100, 100, 105, 116, 105, 111, 110, 97, 108, 32, 96, 103, 114, 105, 110, 100, 96, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__10_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [96, 32, 116, 114, 105, 103, 103, 101, 114, 115, 32, 109, 111, 114, 101, 32, 116, 104, 97, 110, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__1_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,10138443044734372301 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 109, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,7929275688618478524 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,3966920027502889450 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,9418790924191217009 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__4_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,5063646790596052253 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__6_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__7_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__8_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__9_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [116, 114, 97, 99, 101, 46, 103, 114, 105, 110, 100, 46, 101, 109, 97, 116, 99, 104, 46, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__11_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__15_value: crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [84, 114, 121, 32, 116, 104, 105, 115, 32, 116, 111, 32, 100, 105, 115, 112, 108, 97, 121, 32, 116, 104, 101, 32, 97, 99, 116, 117, 97, 108, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 58, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [103, 114, 105, 110, 100, 76, 105, 110, 116, 73, 110, 115, 112, 101, 99, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__0_value) as *mut crate::leanh::LeanObject,627953777420417167 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__0_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 108, 97, 98, 71, 114, 105, 110, 100, 76, 105, 110, 116, 73, 110, 115, 112, 101, 99, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__0_value) as *mut crate::leanh::LeanObject,15857038208080983817 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [95, 114, 111, 111, 116, 95, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,626731335300788152 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [32, 102, 97, 105, 108, 101, 100, 32, 119, 105, 116, 104, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [35, 103, 114, 105, 110, 100, 95, 108, 105, 110, 116, 32, 105, 110, 115, 112, 101, 99, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [84, 114, 121, 32, 116, 104, 105, 115, 58, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [103, 114, 105, 110, 100, 76, 105, 110, 116, 67, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__0_value) as *mut crate::leanh::LeanObject,16879946614306402622 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 108, 97, 98, 71, 114, 105, 110, 100, 76, 105, 110, 116, 67, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__0_value) as *mut crate::leanh::LeanObject,15725561947564143279 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_(
    mut v_es_4135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4136_ = lean_array_mk(v_es_4135_);
    return v___x_4136_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0(
    mut v_as_4137_: *mut crate::leanh::LeanObject,
    mut v_i_4138_: usize,
    mut v_stop_4139_: usize,
    mut v_b_4140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4141_: u8 = 0;
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: usize = 0;
    let mut v___x_4145_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4141_ = lean_usize_dec_eq(v_i_4138_, v_stop_4139_);
                if v___x_4141_ == 0 {
                    v___x_4142_ = lean_array_uget_borrowed(v_as_4137_, v_i_4138_);
                    crate::leanh::lean_inc(v___x_4142_);
                    v___x_4143_ = l_Lean_NameSet_insert(v_b_4140_, v___x_4142_);
                    v___x_4144_ = 1usize;
                    v___x_4145_ = lean_usize_add(v_i_4138_, v___x_4144_);
                    v_i_4138_ = v___x_4145_;
                    v_b_4140_ = v___x_4143_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4140_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_as_4147_: *mut crate::leanh::LeanObject,
    mut v_i_4148_: *mut crate::leanh::LeanObject,
    mut v_stop_4149_: *mut crate::leanh::LeanObject,
    mut v_b_4150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4151_: usize = 0;
    let mut v_stop_boxed_4152_: usize = 0;
    let mut v_res_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4151_ = crate::leanh::lean_unbox_usize(v_i_4148_);
    crate::leanh::lean_dec(v_i_4148_);
    v_stop_boxed_4152_ = crate::leanh::lean_unbox_usize(v_stop_4149_);
    crate::leanh::lean_dec(v_stop_4149_);
    v_res_4153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0(v_as_4147_, v_i_boxed_4151_, v_stop_boxed_4152_, v_b_4150_);
    crate::leanh::lean_dec_ref(v_as_4147_);
    return v_res_4153_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1(
    mut v_as_4154_: *mut crate::leanh::LeanObject,
    mut v_i_4155_: usize,
    mut v_stop_4156_: usize,
    mut v_b_4157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: usize = 0;
    let mut v___x_4161_: usize = 0;
    let mut v___x_4163_: u8 = 0;
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: u8 = 0;
    let mut v___x_4168_: u8 = 0;
    let mut v___x_4169_: usize = 0;
    let mut v___x_4170_: usize = 0;
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: usize = 0;
    let mut v___x_4173_: usize = 0;
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4163_ = lean_usize_dec_eq(v_i_4155_, v_stop_4156_);
                if v___x_4163_ == 0 {
                    v___x_4164_ = lean_array_uget_borrowed(v_as_4154_, v_i_4155_);
                    v___x_4165_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4166_ = lean_array_get_size(v___x_4164_);
                    v___x_4167_ = lean_nat_dec_lt(v___x_4165_, v___x_4166_);
                    if v___x_4167_ == 0 {
                        v___y_4159_ = v_b_4157_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4168_ = lean_nat_dec_le(v___x_4166_, v___x_4166_);
                        if v___x_4168_ == 0 {
                            if v___x_4167_ == 0 {
                                v___y_4159_ = v_b_4157_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4169_ = 0usize;
                                v___x_4170_ = lean_usize_of_nat(v___x_4166_);
                                v___x_4171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0(v___x_4164_, v___x_4169_, v___x_4170_, v_b_4157_);
                                v___y_4159_ = v___x_4171_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_4172_ = 0usize;
                            v___x_4173_ = lean_usize_of_nat(v___x_4166_);
                            v___x_4174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0(v___x_4164_, v___x_4172_, v___x_4173_, v_b_4157_);
                            v___y_4159_ = v___x_4174_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_4157_;
                }
            }
            1 => {
                v___x_4160_ = 1usize;
                v___x_4161_ = lean_usize_add(v_i_4155_, v___x_4160_);
                v_i_4155_ = v___x_4161_;
                v_b_4157_ = v___y_4159_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_as_4175_: *mut crate::leanh::LeanObject,
    mut v_i_4176_: *mut crate::leanh::LeanObject,
    mut v_stop_4177_: *mut crate::leanh::LeanObject,
    mut v_b_4178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4179_: usize = 0;
    let mut v_stop_boxed_4180_: usize = 0;
    let mut v_res_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4179_ = crate::leanh::lean_unbox_usize(v_i_4176_);
    crate::leanh::lean_dec(v_i_4176_);
    v_stop_boxed_4180_ = crate::leanh::lean_unbox_usize(v_stop_4177_);
    crate::leanh::lean_dec(v_stop_4177_);
    v_res_4181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1(v_as_4175_, v_i_boxed_4179_, v_stop_boxed_4180_, v_b_4178_);
    crate::leanh::lean_dec_ref(v_as_4175_);
    return v_res_4181_;
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0(
    mut v_initState_4182_: *mut crate::leanh::LeanObject,
    mut v_as_4183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: u8 = 0;
    v___x_4184_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4185_ = lean_array_get_size(v_as_4183_);
    v___x_4186_ = lean_nat_dec_lt(v___x_4184_, v___x_4185_);
    if v___x_4186_ == 0 {
        return v_initState_4182_;
    } else {
        let mut v___x_4187_: u8 = 0;
        v___x_4187_ = lean_nat_dec_le(v___x_4185_, v___x_4185_);
        if v___x_4187_ == 0 {
            if v___x_4186_ == 0 {
                return v_initState_4182_;
            } else {
                let mut v___x_4188_: usize = 0;
                let mut v___x_4189_: usize = 0;
                let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4188_ = 0usize;
                v___x_4189_ = lean_usize_of_nat(v___x_4185_);
                v___x_4190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1(v_as_4183_, v___x_4188_, v___x_4189_, v_initState_4182_);
                return v___x_4190_;
            }
        } else {
            let mut v___x_4191_: usize = 0;
            let mut v___x_4192_: usize = 0;
            let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4191_ = 0usize;
            v___x_4192_ = lean_usize_of_nat(v___x_4185_);
            v___x_4193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1(v_as_4183_, v___x_4191_, v___x_4192_, v_initState_4182_);
            return v___x_4193_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0___boxed(
    mut v_initState_4194_: *mut crate::leanh::LeanObject,
    mut v_as_4195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4196_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0(v_initState_4194_, v_as_4195_);
    crate::leanh::lean_dec_ref(v_as_4195_);
    return v_res_4196_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4242_ = l_Lean_NameSet_empty;
    v___x_4243_ = crate::leanh::lean_alloc_closure(l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___x_4243_, 0, v___x_4242_);
    return v___x_4243_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4244_ = crate::leanh::lean_box(2);
    v___x_4245_ = crate::leanh::lean_box(0);
    v___f_4246_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_;
    v___x_4247_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_);
    v___f_4248_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_;
    v___x_4249_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_;
    v___x_4250_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4250_, 0, v___x_4249_);
    crate::leanh::lean_ctor_set(v___x_4250_, 1, v___f_4248_);
    crate::leanh::lean_ctor_set(v___x_4250_, 2, v___x_4247_);
    crate::leanh::lean_ctor_set(v___x_4250_, 3, v___f_4246_);
    crate::leanh::lean_ctor_set(v___x_4250_, 4, v___x_4245_);
    crate::leanh::lean_ctor_set(v___x_4250_, 5, v___x_4244_);
    crate::leanh::lean_ctor_set(v___x_4250_, 6, v___x_4245_);
    return v___x_4250_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4252_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_);
    v___x_4253_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_4252_);
    return v___x_4253_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2____boxed(
    mut v_a_4254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4255_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_();
    return v_res_4255_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4260_ = crate::leanh::lean_box(2);
    v___x_4261_ = crate::leanh::lean_box(0);
    v___f_4262_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_;
    v___x_4263_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_);
    v___f_4264_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_;
    v___x_4265_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_;
    v___x_4266_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4266_, 0, v___x_4265_);
    crate::leanh::lean_ctor_set(v___x_4266_, 1, v___f_4264_);
    crate::leanh::lean_ctor_set(v___x_4266_, 2, v___x_4263_);
    crate::leanh::lean_ctor_set(v___x_4266_, 3, v___f_4262_);
    crate::leanh::lean_ctor_set(v___x_4266_, 4, v___x_4261_);
    crate::leanh::lean_ctor_set(v___x_4266_, 5, v___x_4260_);
    crate::leanh::lean_ctor_set(v___x_4266_, 6, v___x_4261_);
    return v___x_4266_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4268_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_);
    v___x_4269_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_4268_);
    return v___x_4269_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2____boxed(
    mut v_a_4270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4271_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_();
    return v_res_4271_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4276_ = crate::leanh::lean_box(2);
    v___x_4277_ = crate::leanh::lean_box(0);
    v___f_4278_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_;
    v___x_4279_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_);
    v___f_4280_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_;
    v___x_4281_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_;
    v___x_4282_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4282_, 0, v___x_4281_);
    crate::leanh::lean_ctor_set(v___x_4282_, 1, v___f_4280_);
    crate::leanh::lean_ctor_set(v___x_4282_, 2, v___x_4279_);
    crate::leanh::lean_ctor_set(v___x_4282_, 3, v___f_4278_);
    crate::leanh::lean_ctor_set(v___x_4282_, 4, v___x_4277_);
    crate::leanh::lean_ctor_set(v___x_4282_, 5, v___x_4276_);
    crate::leanh::lean_ctor_set(v___x_4282_, 6, v___x_4277_);
    return v___x_4282_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4284_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_);
    v___x_4285_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_4284_);
    return v___x_4285_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2____boxed(
    mut v_a_4286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4287_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_();
    return v_res_4287_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4288_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4288_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4289_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0);
    v___x_4290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4290_, 0, v___x_4289_);
    return v___x_4290_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4291_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1);
    v___x_4292_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4293_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4293_, 0, v___x_4292_);
    crate::leanh::lean_ctor_set(v___x_4293_, 1, v___x_4292_);
    crate::leanh::lean_ctor_set(v___x_4293_, 2, v___x_4292_);
    crate::leanh::lean_ctor_set(v___x_4293_, 3, v___x_4292_);
    crate::leanh::lean_ctor_set(v___x_4293_, 4, v___x_4291_);
    crate::leanh::lean_ctor_set(v___x_4293_, 5, v___x_4291_);
    crate::leanh::lean_ctor_set(v___x_4293_, 6, v___x_4291_);
    crate::leanh::lean_ctor_set(v___x_4293_, 7, v___x_4291_);
    crate::leanh::lean_ctor_set(v___x_4293_, 8, v___x_4291_);
    crate::leanh::lean_ctor_set(v___x_4293_, 9, v___x_4291_);
    return v___x_4293_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4294_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4295_ = lean_mk_empty_array_with_capacity(v___x_4294_);
    v___x_4296_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4296_, 0, v___x_4295_);
    return v___x_4296_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4297_: usize = 0;
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4297_ = 5usize;
    v___x_4298_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4299_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4300_ = lean_mk_empty_array_with_capacity(v___x_4299_);
    v___x_4301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3);
    v___x_4302_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4302_, 0, v___x_4301_);
    crate::leanh::lean_ctor_set(v___x_4302_, 1, v___x_4300_);
    crate::leanh::lean_ctor_set(v___x_4302_, 2, v___x_4298_);
    crate::leanh::lean_ctor_set(v___x_4302_, 3, v___x_4298_);
    crate::leanh::lean_ctor_set_usize(v___x_4302_, 4, v___x_4297_);
    return v___x_4302_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4303_ = crate::leanh::lean_box(1);
    v___x_4304_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4);
    v___x_4305_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1);
    v___x_4306_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4306_, 0, v___x_4305_);
    crate::leanh::lean_ctor_set(v___x_4306_, 1, v___x_4304_);
    crate::leanh::lean_ctor_set(v___x_4306_, 2, v___x_4303_);
    return v___x_4306_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(
    mut v_msgData_4307_: *mut crate::leanh::LeanObject,
    mut v___y_4308_: *mut crate::leanh::LeanObject,
    mut v___y_4309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4311_ = lean_st_ref_get(v___y_4309_);
    v_env_4312_ = crate::leanh::lean_ctor_get(v___x_4311_, 0);
    crate::leanh::lean_inc_ref(v_env_4312_);
    crate::leanh::lean_dec(v___x_4311_);
    v_options_4313_ = crate::leanh::lean_ctor_get(v___y_4308_, 2);
    v___x_4314_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2);
    v___x_4315_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5);
    crate::leanh::lean_inc_ref(v_options_4313_);
    v___x_4316_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4316_, 0, v_env_4312_);
    crate::leanh::lean_ctor_set(v___x_4316_, 1, v___x_4314_);
    crate::leanh::lean_ctor_set(v___x_4316_, 2, v___x_4315_);
    crate::leanh::lean_ctor_set(v___x_4316_, 3, v_options_4313_);
    v___x_4317_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4317_, 0, v___x_4316_);
    crate::leanh::lean_ctor_set(v___x_4317_, 1, v_msgData_4307_);
    v___x_4318_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4318_, 0, v___x_4317_);
    return v___x_4318_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___boxed(
    mut v_msgData_4319_: *mut crate::leanh::LeanObject,
    mut v___y_4320_: *mut crate::leanh::LeanObject,
    mut v___y_4321_: *mut crate::leanh::LeanObject,
    mut v___y_4322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4323_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(v_msgData_4319_, v___y_4320_, v___y_4321_);
    crate::leanh::lean_dec(v___y_4321_);
    crate::leanh::lean_dec_ref(v___y_4320_);
    return v_res_4323_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(
    mut v_msg_4324_: *mut crate::leanh::LeanObject,
    mut v___y_4325_: *mut crate::leanh::LeanObject,
    mut v___y_4326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4333_: u8 = 0;
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4328_ = crate::leanh::lean_ctor_get(v___y_4325_, 5);
                v___x_4329_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(v_msg_4324_, v___y_4325_, v___y_4326_);
                v_a_4330_ = crate::leanh::lean_ctor_get(v___x_4329_, 0);
                v_isSharedCheck_4338_ = (!crate::leanh::lean_is_exclusive(v___x_4329_)) as u8;
                if v_isSharedCheck_4338_ == 0 {
                    v___x_4332_ = v___x_4329_;
                    v_isShared_4333_ = v_isSharedCheck_4338_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4330_);
                    crate::leanh::lean_dec(v___x_4329_);
                    v___x_4332_ = crate::leanh::lean_box(0);
                    v_isShared_4333_ = v_isSharedCheck_4338_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4328_);
                v___x_4334_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4334_, 0, v_ref_4328_);
                crate::leanh::lean_ctor_set(v___x_4334_, 1, v_a_4330_);
                if v_isShared_4333_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4332_, 1);
                    crate::leanh::lean_ctor_set(v___x_4332_, 0, v___x_4334_);
                    v___x_4336_ = v___x_4332_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4334_);
                    v___x_4336_ = v_reuseFailAlloc_4337_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg___boxed(
    mut v_msg_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
    mut v___y_4341_: *mut crate::leanh::LeanObject,
    mut v___y_4342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4343_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(v_msg_4339_, v___y_4340_, v___y_4341_);
    crate::leanh::lean_dec(v___y_4341_);
    crate::leanh::lean_dec_ref(v___y_4340_);
    return v_res_4343_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4345_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__0;
    v___x_4346_ = l_Lean_stringToMessageData(v___x_4345_);
    return v___x_4346_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4348_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__2;
    v___x_4349_ = l_Lean_stringToMessageData(v___x_4348_);
    return v___x_4349_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(
    mut v_declName_4350_: *mut crate::leanh::LeanObject,
    mut v_a_4351_: *mut crate::leanh::LeanObject,
    mut v_a_4352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4359_: u8 = 0;
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4371_: u8 = 0;
    let mut v_a_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4375_: u8 = 0;
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4354_ = l_Lean_Meta_Grind_grindExt;
                crate::leanh::lean_inc(v_declName_4350_);
                v___x_4355_ = l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(
                    v___x_4354_,
                    v_declName_4350_,
                    v_a_4352_,
                );
                if crate::leanh::lean_obj_tag(v___x_4355_) == 0 {
                    v_a_4356_ = crate::leanh::lean_ctor_get(v___x_4355_, 0);
                    v_isSharedCheck_4371_ = (!crate::leanh::lean_is_exclusive(v___x_4355_)) as u8;
                    if v_isSharedCheck_4371_ == 0 {
                        v___x_4358_ = v___x_4355_;
                        v_isShared_4359_ = v_isSharedCheck_4371_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4356_);
                        crate::leanh::lean_dec(v___x_4355_);
                        v___x_4358_ = crate::leanh::lean_box(0);
                        v_isShared_4359_ = v_isSharedCheck_4371_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_4350_);
                    v_a_4372_ = crate::leanh::lean_ctor_get(v___x_4355_, 0);
                    v_isSharedCheck_4379_ = (!crate::leanh::lean_is_exclusive(v___x_4355_)) as u8;
                    if v_isSharedCheck_4379_ == 0 {
                        v___x_4374_ = v___x_4355_;
                        v_isShared_4375_ = v_isSharedCheck_4379_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4372_);
                        crate::leanh::lean_dec(v___x_4355_);
                        v___x_4374_ = crate::leanh::lean_box(0);
                        v_isShared_4375_ = v_isSharedCheck_4379_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4360_ = (crate::leanh::lean_unbox(v_a_4356_) as u8);
                crate::leanh::lean_dec(v_a_4356_);
                if v___x_4360_ == 0 {
                    crate::leanh::lean_del_object(v___x_4358_);
                    v___x_4361_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
                    v___x_4362_ = l_Lean_MessageData_ofName(v_declName_4350_);
                    v___x_4363_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4363_, 0, v___x_4361_);
                    crate::leanh::lean_ctor_set(v___x_4363_, 1, v___x_4362_);
                    v___x_4364_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3);
                    v___x_4365_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4365_, 0, v___x_4363_);
                    crate::leanh::lean_ctor_set(v___x_4365_, 1, v___x_4364_);
                    v___x_4366_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(v___x_4365_, v_a_4351_, v_a_4352_);
                    return v___x_4366_;
                } else {
                    crate::leanh::lean_dec(v_declName_4350_);
                    v___x_4367_ = crate::leanh::lean_box(0);
                    if v_isShared_4359_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4358_, 0, v___x_4367_);
                        v___x_4369_ = v___x_4358_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4370_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
                        v___x_4369_ = v_reuseFailAlloc_4370_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4369_;
            }
            3 => {
                if v_isShared_4375_ == 0 {
                    v___x_4377_ = v___x_4374_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
                    v___x_4377_ = v_reuseFailAlloc_4378_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___boxed(
    mut v_declName_4380_: *mut crate::leanh::LeanObject,
    mut v_a_4381_: *mut crate::leanh::LeanObject,
    mut v_a_4382_: *mut crate::leanh::LeanObject,
    mut v_a_4383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4384_ =
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(
            v_declName_4380_,
            v_a_4381_,
            v_a_4382_,
        );
    crate::leanh::lean_dec(v_a_4382_);
    crate::leanh::lean_dec_ref(v_a_4381_);
    return v_res_4384_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0(
    mut v_00_u03b1_4385_: *mut crate::leanh::LeanObject,
    mut v_msg_4386_: *mut crate::leanh::LeanObject,
    mut v___y_4387_: *mut crate::leanh::LeanObject,
    mut v___y_4388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4390_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(v_msg_4386_, v___y_4387_, v___y_4388_);
    return v___x_4390_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___boxed(
    mut v_00_u03b1_4391_: *mut crate::leanh::LeanObject,
    mut v_msg_4392_: *mut crate::leanh::LeanObject,
    mut v___y_4393_: *mut crate::leanh::LeanObject,
    mut v___y_4394_: *mut crate::leanh::LeanObject,
    mut v___y_4395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4396_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0(v_00_u03b1_4391_, v_msg_4392_, v___y_4393_, v___y_4394_);
    crate::leanh::lean_dec(v___y_4394_);
    crate::leanh::lean_dec_ref(v___y_4393_);
    return v_res_4396_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4397_ = crate::leanh::lean_box(0);
    v___x_4398_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_4399_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4399_, 0, v___x_4398_);
    crate::leanh::lean_ctor_set(v___x_4399_, 1, v___x_4397_);
    return v___x_4399_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4401_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0);
    v___x_4402_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4402_, 0, v___x_4401_);
    return v___x_4402_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___boxed(
    mut v___y_4403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4404_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
    return v_res_4404_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(
    mut v_00_u03b1_4405_: *mut crate::leanh::LeanObject,
    mut v___y_4406_: *mut crate::leanh::LeanObject,
    mut v___y_4407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4409_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
    return v___x_4409_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___boxed(
    mut v_00_u03b1_4410_: *mut crate::leanh::LeanObject,
    mut v___y_4411_: *mut crate::leanh::LeanObject,
    mut v___y_4412_: *mut crate::leanh::LeanObject,
    mut v___y_4413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4414_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(v_00_u03b1_4410_, v___y_4411_, v___y_4412_);
    crate::leanh::lean_dec(v___y_4412_);
    crate::leanh::lean_dec_ref(v___y_4411_);
    return v_res_4414_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(
    mut v_msgData_4415_: *mut crate::leanh::LeanObject,
    mut v___y_4416_: *mut crate::leanh::LeanObject,
    mut v___y_4417_: *mut crate::leanh::LeanObject,
    mut v___y_4418_: *mut crate::leanh::LeanObject,
    mut v___y_4419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4421_ = lean_st_ref_get(v___y_4419_);
    v_env_4422_ = crate::leanh::lean_ctor_get(v___x_4421_, 0);
    crate::leanh::lean_inc_ref(v_env_4422_);
    crate::leanh::lean_dec(v___x_4421_);
    v___x_4423_ = lean_st_ref_get(v___y_4417_);
    v_mctx_4424_ = crate::leanh::lean_ctor_get(v___x_4423_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4424_);
    crate::leanh::lean_dec(v___x_4423_);
    v_lctx_4425_ = crate::leanh::lean_ctor_get(v___y_4416_, 2);
    v_options_4426_ = crate::leanh::lean_ctor_get(v___y_4418_, 2);
    crate::leanh::lean_inc_ref(v_options_4426_);
    crate::leanh::lean_inc_ref(v_lctx_4425_);
    v___x_4427_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4427_, 0, v_env_4422_);
    crate::leanh::lean_ctor_set(v___x_4427_, 1, v_mctx_4424_);
    crate::leanh::lean_ctor_set(v___x_4427_, 2, v_lctx_4425_);
    crate::leanh::lean_ctor_set(v___x_4427_, 3, v_options_4426_);
    v___x_4428_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4428_, 0, v___x_4427_);
    crate::leanh::lean_ctor_set(v___x_4428_, 1, v_msgData_4415_);
    v___x_4429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4429_, 0, v___x_4428_);
    return v___x_4429_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___boxed(
    mut v_msgData_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
    mut v___y_4433_: *mut crate::leanh::LeanObject,
    mut v___y_4434_: *mut crate::leanh::LeanObject,
    mut v___y_4435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4436_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v_msgData_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
    crate::leanh::lean_dec(v___y_4434_);
    crate::leanh::lean_dec_ref(v___y_4433_);
    crate::leanh::lean_dec(v___y_4432_);
    crate::leanh::lean_dec_ref(v___y_4431_);
    return v_res_4436_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(
    mut v_opts_4437_: *mut crate::leanh::LeanObject,
    mut v_opt_4438_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4439_ = crate::leanh::lean_ctor_get(v_opt_4438_, 0);
    v_defValue_4440_ = crate::leanh::lean_ctor_get(v_opt_4438_, 1);
    v_map_4441_ = crate::leanh::lean_ctor_get(v_opts_4437_, 0);
    v___x_4442_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4441_,
            v_name_4439_,
        );
    if crate::leanh::lean_obj_tag(v___x_4442_) == 0 {
        let mut v___x_4443_: u8 = 0;
        v___x_4443_ = (crate::leanh::lean_unbox(v_defValue_4440_) as u8);
        return v___x_4443_;
    } else {
        let mut v_val_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4444_ = crate::leanh::lean_ctor_get(v___x_4442_, 0);
        crate::leanh::lean_inc(v_val_4444_);
        crate::leanh::lean_dec_ref_known(v___x_4442_, 1);
        if crate::leanh::lean_obj_tag(v_val_4444_) == 1 {
            let mut v_v_4445_: u8 = 0;
            v_v_4445_ = crate::leanh::lean_ctor_get_uint8(v_val_4444_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_4444_, 0);
            return v_v_4445_;
        } else {
            let mut v___x_4446_: u8 = 0;
            crate::leanh::lean_dec(v_val_4444_);
            v___x_4446_ = (crate::leanh::lean_unbox(v_defValue_4440_) as u8);
            return v___x_4446_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3___boxed(
    mut v_opts_4447_: *mut crate::leanh::LeanObject,
    mut v_opt_4448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4449_: u8 = 0;
    let mut v_r_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4449_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(v_opts_4447_, v_opt_4448_);
    crate::leanh::lean_dec_ref(v_opt_4448_);
    crate::leanh::lean_dec_ref(v_opts_4447_);
    v_r_4450_ = crate::leanh::lean_box((v_res_4449_) as usize);
    return v_r_4450_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4451_ = crate::leanh::lean_box(1);
    v___x_4452_ = l_Lean_MessageData_ofFormat(v___x_4451_);
    return v___x_4452_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4456_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__2;
    v___x_4457_ = l_Lean_MessageData_ofFormat(v___x_4456_);
    return v___x_4457_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4(
    mut v_x_4458_: *mut crate::leanh::LeanObject,
    mut v_x_4459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4464_: u8 = 0;
    let mut v_before_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4468_: u8 = 0;
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4481_: u8 = 0;
    let mut v_unused_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4459_) == 0 {
                    return v_x_4458_;
                } else {
                    v_head_4460_ = crate::leanh::lean_ctor_get(v_x_4459_, 0);
                    v_tail_4461_ = crate::leanh::lean_ctor_get(v_x_4459_, 1);
                    v_isSharedCheck_4483_ = (!crate::leanh::lean_is_exclusive(v_x_4459_)) as u8;
                    if v_isSharedCheck_4483_ == 0 {
                        v___x_4463_ = v_x_4459_;
                        v_isShared_4464_ = v_isSharedCheck_4483_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4461_);
                        crate::leanh::lean_inc(v_head_4460_);
                        crate::leanh::lean_dec(v_x_4459_);
                        v___x_4463_ = crate::leanh::lean_box(0);
                        v_isShared_4464_ = v_isSharedCheck_4483_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_4465_ = crate::leanh::lean_ctor_get(v_head_4460_, 0);
                v_isSharedCheck_4481_ = (!crate::leanh::lean_is_exclusive(v_head_4460_)) as u8;
                if v_isSharedCheck_4481_ == 0 {
                    v_unused_4482_ = crate::leanh::lean_ctor_get(v_head_4460_, 1);
                    crate::leanh::lean_dec(v_unused_4482_);
                    v___x_4467_ = v_head_4460_;
                    v_isShared_4468_ = v_isSharedCheck_4481_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_4465_);
                    crate::leanh::lean_dec(v_head_4460_);
                    v___x_4467_ = crate::leanh::lean_box(0);
                    v_isShared_4468_ = v_isSharedCheck_4481_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4469_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0);
                if v_isShared_4468_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4467_, 7);
                    crate::leanh::lean_ctor_set(v___x_4467_, 1, v___x_4469_);
                    crate::leanh::lean_ctor_set(v___x_4467_, 0, v_x_4458_);
                    v___x_4471_ = v___x_4467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4480_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_x_4458_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 1, v___x_4469_);
                    v___x_4471_ = v_reuseFailAlloc_4480_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4472_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3);
                if v_isShared_4464_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4463_, 7);
                    crate::leanh::lean_ctor_set(v___x_4463_, 1, v___x_4472_);
                    crate::leanh::lean_ctor_set(v___x_4463_, 0, v___x_4471_);
                    v___x_4474_ = v___x_4463_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4479_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4479_, 1, v___x_4472_);
                    v___x_4474_ = v_reuseFailAlloc_4479_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4475_ = l_Lean_MessageData_ofSyntax(v_before_4465_);
                v___x_4476_ = l_Lean_indentD(v___x_4475_);
                v___x_4477_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4477_, 0, v___x_4474_);
                crate::leanh::lean_ctor_set(v___x_4477_, 1, v___x_4476_);
                v_x_4458_ = v___x_4477_;
                v_x_4459_ = v_tail_4461_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4487_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__1;
    v___x_4488_ = l_Lean_MessageData_ofFormat(v___x_4487_);
    return v___x_4488_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(
    mut v_msgData_4489_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4490_: *mut crate::leanh::LeanObject,
    mut v___y_4491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: u8 = 0;
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut v_unused_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4493_ = crate::leanh::lean_ctor_get(v___y_4491_, 2);
                v___x_4494_ = l_Lean_Elab_pp_macroStack;
                v___x_4495_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(v_options_4493_, v___x_4494_);
                if v___x_4495_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_4490_);
                    v___x_4496_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4496_, 0, v_msgData_4489_);
                    return v___x_4496_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_4490_) == 0 {
                        v___x_4497_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4497_, 0, v_msgData_4489_);
                        return v___x_4497_;
                    } else {
                        v_head_4498_ = crate::leanh::lean_ctor_get(v_macroStack_4490_, 0);
                        crate::leanh::lean_inc(v_head_4498_);
                        v_after_4499_ = crate::leanh::lean_ctor_get(v_head_4498_, 1);
                        v_isSharedCheck_4514_ =
                            (!crate::leanh::lean_is_exclusive(v_head_4498_)) as u8;
                        if v_isSharedCheck_4514_ == 0 {
                            v_unused_4515_ = crate::leanh::lean_ctor_get(v_head_4498_, 0);
                            crate::leanh::lean_dec(v_unused_4515_);
                            v___x_4501_ = v_head_4498_;
                            v_isShared_4502_ = v_isSharedCheck_4514_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_4499_);
                            crate::leanh::lean_dec(v_head_4498_);
                            v___x_4501_ = crate::leanh::lean_box(0);
                            v_isShared_4502_ = v_isSharedCheck_4514_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4503_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0);
                if v_isShared_4502_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4501_, 7);
                    crate::leanh::lean_ctor_set(v___x_4501_, 1, v___x_4503_);
                    crate::leanh::lean_ctor_set(v___x_4501_, 0, v_msgData_4489_);
                    v___x_4505_ = v___x_4501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4513_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_msgData_4489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4513_, 1, v___x_4503_);
                    v___x_4505_ = v_reuseFailAlloc_4513_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4506_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2);
                v___x_4507_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4507_, 0, v___x_4505_);
                crate::leanh::lean_ctor_set(v___x_4507_, 1, v___x_4506_);
                v___x_4508_ = l_Lean_MessageData_ofSyntax(v_after_4499_);
                v___x_4509_ = l_Lean_indentD(v___x_4508_);
                v_msgData_4510_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_4510_, 0, v___x_4507_);
                crate::leanh::lean_ctor_set(v_msgData_4510_, 1, v___x_4509_);
                v___x_4511_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4(v_msgData_4510_, v_macroStack_4490_);
                v___x_4512_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4512_, 0, v___x_4511_);
                return v___x_4512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___boxed(
    mut v_msgData_4516_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4520_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(v_msgData_4516_, v_macroStack_4517_, v___y_4518_);
    crate::leanh::lean_dec_ref(v___y_4518_);
    return v_res_4520_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(
    mut v_msg_4521_: *mut crate::leanh::LeanObject,
    mut v___y_4522_: *mut crate::leanh::LeanObject,
    mut v___y_4523_: *mut crate::leanh::LeanObject,
    mut v___y_4524_: *mut crate::leanh::LeanObject,
    mut v___y_4525_: *mut crate::leanh::LeanObject,
    mut v___y_4526_: *mut crate::leanh::LeanObject,
    mut v___y_4527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4538_: u8 = 0;
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4529_ = crate::leanh::lean_ctor_get(v___y_4526_, 5);
                v___x_4530_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v_msg_4521_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
                v_a_4531_ = crate::leanh::lean_ctor_get(v___x_4530_, 0);
                crate::leanh::lean_inc(v_a_4531_);
                crate::leanh::lean_dec_ref(v___x_4530_);
                v_macroStack_4532_ = crate::leanh::lean_ctor_get(v___y_4522_, 1);
                v___x_4533_ = l_Lean_Elab_getBetterRef(v_ref_4529_, v_macroStack_4532_);
                crate::leanh::lean_inc(v_macroStack_4532_);
                v___x_4534_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(v_a_4531_, v_macroStack_4532_, v___y_4526_);
                v_a_4535_ = crate::leanh::lean_ctor_get(v___x_4534_, 0);
                v_isSharedCheck_4543_ = (!crate::leanh::lean_is_exclusive(v___x_4534_)) as u8;
                if v_isSharedCheck_4543_ == 0 {
                    v___x_4537_ = v___x_4534_;
                    v_isShared_4538_ = v_isSharedCheck_4543_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4535_);
                    crate::leanh::lean_dec(v___x_4534_);
                    v___x_4537_ = crate::leanh::lean_box(0);
                    v_isShared_4538_ = v_isSharedCheck_4543_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4539_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4539_, 0, v___x_4533_);
                crate::leanh::lean_ctor_set(v___x_4539_, 1, v_a_4535_);
                if v_isShared_4538_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4537_, 1);
                    crate::leanh::lean_ctor_set(v___x_4537_, 0, v___x_4539_);
                    v___x_4541_ = v___x_4537_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4542_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4539_);
                    v___x_4541_ = v_reuseFailAlloc_4542_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg___boxed(
    mut v_msg_4544_: *mut crate::leanh::LeanObject,
    mut v___y_4545_: *mut crate::leanh::LeanObject,
    mut v___y_4546_: *mut crate::leanh::LeanObject,
    mut v___y_4547_: *mut crate::leanh::LeanObject,
    mut v___y_4548_: *mut crate::leanh::LeanObject,
    mut v___y_4549_: *mut crate::leanh::LeanObject,
    mut v___y_4550_: *mut crate::leanh::LeanObject,
    mut v___y_4551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4552_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v_msg_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
    crate::leanh::lean_dec(v___y_4550_);
    crate::leanh::lean_dec_ref(v___y_4549_);
    crate::leanh::lean_dec(v___y_4548_);
    crate::leanh::lean_dec_ref(v___y_4547_);
    crate::leanh::lean_dec(v___y_4546_);
    crate::leanh::lean_dec_ref(v___y_4545_);
    return v_res_4552_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4553_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4553_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4554_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0);
    v___x_4555_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4555_, 0, v___x_4554_);
    return v___x_4555_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4556_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1);
    v___x_4557_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4557_, 0, v___x_4556_);
    crate::leanh::lean_ctor_set(v___x_4557_, 1, v___x_4556_);
    return v___x_4557_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4558_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1);
    v___x_4559_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4559_, 0, v___x_4558_);
    crate::leanh::lean_ctor_set(v___x_4559_, 1, v___x_4558_);
    crate::leanh::lean_ctor_set(v___x_4559_, 2, v___x_4558_);
    crate::leanh::lean_ctor_set(v___x_4559_, 3, v___x_4558_);
    crate::leanh::lean_ctor_set(v___x_4559_, 4, v___x_4558_);
    crate::leanh::lean_ctor_set(v___x_4559_, 5, v___x_4558_);
    return v___x_4559_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4;
    v___x_4562_ = l_Lean_stringToMessageData(v___x_4561_);
    return v___x_4562_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(
    mut v_as_4563_: *mut crate::leanh::LeanObject,
    mut v_sz_4564_: usize,
    mut v_i_4565_: usize,
    mut v_b_4566_: *mut crate::leanh::LeanObject,
    mut v___y_4567_: *mut crate::leanh::LeanObject,
    mut v___y_4568_: *mut crate::leanh::LeanObject,
    mut v___y_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
    mut v___y_4572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4574_: u8 = 0;
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4602_: u8 = 0;
    let mut v_asyncMode_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4617_: u8 = 0;
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: usize = 0;
    let mut v___x_4623_: usize = 0;
    let mut v_reuseFailAlloc_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut v_unused_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4629_: u8 = 0;
    let mut v_unused_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: u8 = 0;
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4644_: u8 = 0;
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4574_ = lean_usize_dec_lt(v_i_4565_, v_sz_4564_);
                if v___x_4574_ == 0 {
                    v___x_4575_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4575_, 0, v_b_4566_);
                    return v___x_4575_;
                } else {
                    v_a_4576_ = lean_array_uget_borrowed(v_as_4563_, v_i_4565_);
                    v___x_4577_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_4576_);
                    v___x_4578_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                        v_a_4576_,
                        v___x_4577_,
                        v___y_4571_,
                        v___y_4572_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4578_) == 0 {
                        v_a_4579_ = crate::leanh::lean_ctor_get(v___x_4578_, 0);
                        crate::leanh::lean_inc_n(v_a_4579_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4578_, 1);
                        v___x_4580_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_a_4579_, v___y_4571_, v___y_4572_);
                        if crate::leanh::lean_obj_tag(v___x_4580_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4580_, 1);
                            v___x_4581_ = lean_st_ref_get(v___y_4572_);
                            v_env_4582_ = crate::leanh::lean_ctor_get(v___x_4581_, 0);
                            crate::leanh::lean_inc_ref(v_env_4582_);
                            crate::leanh::lean_dec(v___x_4581_);
                            v___x_4583_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
                            v_toEnvExtension_4584_ = crate::leanh::lean_ctor_get(v___x_4583_, 0);
                            v_asyncMode_4585_ =
                                crate::leanh::lean_ctor_get(v_toEnvExtension_4584_, 2);
                            v___x_4586_ = crate::leanh::lean_box(0);
                            v___x_4631_ = crate::leanh::lean_box(1);
                            v___x_4632_ = crate::leanh::lean_box(0);
                            v___x_4633_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                                v___x_4631_,
                                v___x_4583_,
                                v_env_4582_,
                                v_asyncMode_4585_,
                                v___x_4632_,
                            );
                            v___x_4634_ = l_Lean_NameSet_contains(v___x_4633_, v_a_4579_);
                            crate::leanh::lean_dec(v___x_4633_);
                            if v___x_4634_ == 0 {
                                v___y_4588_ = v___y_4570_;
                                v___y_4589_ = v___y_4572_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4635_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
                                crate::leanh::lean_inc(v_a_4579_);
                                v___x_4636_ = l_Lean_MessageData_ofName(v_a_4579_);
                                v___x_4637_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4637_, 0, v___x_4635_);
                                crate::leanh::lean_ctor_set(v___x_4637_, 1, v___x_4636_);
                                v___x_4638_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__5);
                                v___x_4639_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4639_, 0, v___x_4637_);
                                crate::leanh::lean_ctor_set(v___x_4639_, 1, v___x_4638_);
                                v___x_4640_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v___x_4639_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
                                if crate::leanh::lean_obj_tag(v___x_4640_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4640_, 1);
                                    v___y_4588_ = v___y_4570_;
                                    v___y_4589_ = v___y_4572_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_4579_);
                                    return v___x_4640_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4579_);
                            return v___x_4580_;
                        }
                    } else {
                        v_a_4641_ = crate::leanh::lean_ctor_get(v___x_4578_, 0);
                        v_isSharedCheck_4648_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4578_)) as u8;
                        if v_isSharedCheck_4648_ == 0 {
                            v___x_4643_ = v___x_4578_;
                            v_isShared_4644_ = v_isSharedCheck_4648_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4641_);
                            crate::leanh::lean_dec(v___x_4578_);
                            v___x_4643_ = crate::leanh::lean_box(0);
                            v_isShared_4644_ = v_isSharedCheck_4648_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4590_ = lean_st_ref_take(v___y_4589_);
                v_toEnvExtension_4591_ = crate::leanh::lean_ctor_get(v___x_4583_, 0);
                v_env_4592_ = crate::leanh::lean_ctor_get(v___x_4590_, 0);
                v_nextMacroScope_4593_ = crate::leanh::lean_ctor_get(v___x_4590_, 1);
                v_ngen_4594_ = crate::leanh::lean_ctor_get(v___x_4590_, 2);
                v_auxDeclNGen_4595_ = crate::leanh::lean_ctor_get(v___x_4590_, 3);
                v_traceState_4596_ = crate::leanh::lean_ctor_get(v___x_4590_, 4);
                v_messages_4597_ = crate::leanh::lean_ctor_get(v___x_4590_, 6);
                v_infoState_4598_ = crate::leanh::lean_ctor_get(v___x_4590_, 7);
                v_snapshotTasks_4599_ = crate::leanh::lean_ctor_get(v___x_4590_, 8);
                v_isSharedCheck_4629_ = (!crate::leanh::lean_is_exclusive(v___x_4590_)) as u8;
                if v_isSharedCheck_4629_ == 0 {
                    v_unused_4630_ = crate::leanh::lean_ctor_get(v___x_4590_, 5);
                    crate::leanh::lean_dec(v_unused_4630_);
                    v___x_4601_ = v___x_4590_;
                    v_isShared_4602_ = v_isSharedCheck_4629_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4599_);
                    crate::leanh::lean_inc(v_infoState_4598_);
                    crate::leanh::lean_inc(v_messages_4597_);
                    crate::leanh::lean_inc(v_traceState_4596_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4595_);
                    crate::leanh::lean_inc(v_ngen_4594_);
                    crate::leanh::lean_inc(v_nextMacroScope_4593_);
                    crate::leanh::lean_inc(v_env_4592_);
                    crate::leanh::lean_dec(v___x_4590_);
                    v___x_4601_ = crate::leanh::lean_box(0);
                    v_isShared_4602_ = v_isSharedCheck_4629_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4603_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4591_, 2);
                v___x_4604_ = crate::leanh::lean_box(0);
                v___x_4605_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4583_,
                    v_env_4592_,
                    v_a_4579_,
                    v_asyncMode_4603_,
                    v___x_4604_,
                );
                v___x_4606_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2);
                if v_isShared_4602_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4601_, 5, v___x_4606_);
                    crate::leanh::lean_ctor_set(v___x_4601_, 0, v___x_4605_);
                    v___x_4608_ = v___x_4601_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4628_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4605_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4628_, 1, v_nextMacroScope_4593_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4628_, 2, v_ngen_4594_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4628_, 3, v_auxDeclNGen_4595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4628_, 4, v_traceState_4596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4628_, 5, v___x_4606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4628_, 6, v_messages_4597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4628_, 7, v_infoState_4598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4628_, 8, v_snapshotTasks_4599_);
                    v___x_4608_ = v_reuseFailAlloc_4628_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4609_ = lean_st_ref_set(v___y_4589_, v___x_4608_);
                v___x_4610_ = lean_st_ref_take(v___y_4588_);
                v_mctx_4611_ = crate::leanh::lean_ctor_get(v___x_4610_, 0);
                v_zetaDeltaFVarIds_4612_ = crate::leanh::lean_ctor_get(v___x_4610_, 2);
                v_postponed_4613_ = crate::leanh::lean_ctor_get(v___x_4610_, 3);
                v_diag_4614_ = crate::leanh::lean_ctor_get(v___x_4610_, 4);
                v_isSharedCheck_4626_ = (!crate::leanh::lean_is_exclusive(v___x_4610_)) as u8;
                if v_isSharedCheck_4626_ == 0 {
                    v_unused_4627_ = crate::leanh::lean_ctor_get(v___x_4610_, 1);
                    crate::leanh::lean_dec(v_unused_4627_);
                    v___x_4616_ = v___x_4610_;
                    v_isShared_4617_ = v_isSharedCheck_4626_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4614_);
                    crate::leanh::lean_inc(v_postponed_4613_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4612_);
                    crate::leanh::lean_inc(v_mctx_4611_);
                    crate::leanh::lean_dec(v___x_4610_);
                    v___x_4616_ = crate::leanh::lean_box(0);
                    v_isShared_4617_ = v_isSharedCheck_4626_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4618_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3);
                if v_isShared_4617_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4616_, 1, v___x_4618_);
                    v___x_4620_ = v___x_4616_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4625_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_mctx_4611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 1, v___x_4618_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4625_,
                        2,
                        v_zetaDeltaFVarIds_4612_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 3, v_postponed_4613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 4, v_diag_4614_);
                    v___x_4620_ = v_reuseFailAlloc_4625_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4621_ = lean_st_ref_set(v___y_4588_, v___x_4620_);
                v___x_4622_ = 1usize;
                v___x_4623_ = lean_usize_add(v_i_4565_, v___x_4622_);
                v_i_4565_ = v___x_4623_;
                v_b_4566_ = v___x_4586_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_4644_ == 0 {
                    v___x_4646_ = v___x_4643_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4647_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
                    v___x_4646_ = v_reuseFailAlloc_4647_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___boxed(
    mut v_as_4649_: *mut crate::leanh::LeanObject,
    mut v_sz_4650_: *mut crate::leanh::LeanObject,
    mut v_i_4651_: *mut crate::leanh::LeanObject,
    mut v_b_4652_: *mut crate::leanh::LeanObject,
    mut v___y_4653_: *mut crate::leanh::LeanObject,
    mut v___y_4654_: *mut crate::leanh::LeanObject,
    mut v___y_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
    mut v___y_4659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4660_: usize = 0;
    let mut v_i_boxed_4661_: usize = 0;
    let mut v_res_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4660_ = crate::leanh::lean_unbox_usize(v_sz_4650_);
    crate::leanh::lean_dec(v_sz_4650_);
    v_i_boxed_4661_ = crate::leanh::lean_unbox_usize(v_i_4651_);
    crate::leanh::lean_dec(v_i_4651_);
    v_res_4662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(v_as_4649_, v_sz_boxed_4660_, v_i_boxed_4661_, v_b_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
    crate::leanh::lean_dec(v___y_4658_);
    crate::leanh::lean_dec_ref(v___y_4657_);
    crate::leanh::lean_dec(v___y_4656_);
    crate::leanh::lean_dec_ref(v___y_4655_);
    crate::leanh::lean_dec(v___y_4654_);
    crate::leanh::lean_dec_ref(v___y_4653_);
    crate::leanh::lean_dec_ref(v_as_4649_);
    return v_res_4662_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0;
    v___x_4665_ = l_Lean_stringToMessageData(v___x_4664_);
    return v___x_4665_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(
    mut v_as_4666_: *mut crate::leanh::LeanObject,
    mut v_sz_4667_: usize,
    mut v_i_4668_: usize,
    mut v_b_4669_: *mut crate::leanh::LeanObject,
    mut v___y_4670_: *mut crate::leanh::LeanObject,
    mut v___y_4671_: *mut crate::leanh::LeanObject,
    mut v___y_4672_: *mut crate::leanh::LeanObject,
    mut v___y_4673_: *mut crate::leanh::LeanObject,
    mut v___y_4674_: *mut crate::leanh::LeanObject,
    mut v___y_4675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4677_: u8 = 0;
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4702_: u8 = 0;
    let mut v_asyncMode_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4717_: u8 = 0;
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: usize = 0;
    let mut v___x_4723_: usize = 0;
    let mut v_reuseFailAlloc_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4726_: u8 = 0;
    let mut v_unused_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4729_: u8 = 0;
    let mut v_unused_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: u8 = 0;
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4677_ = lean_usize_dec_lt(v_i_4668_, v_sz_4667_);
                if v___x_4677_ == 0 {
                    v___x_4678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4678_, 0, v_b_4669_);
                    return v___x_4678_;
                } else {
                    v___x_4679_ = lean_st_ref_get(v___y_4675_);
                    v_env_4680_ = crate::leanh::lean_ctor_get(v___x_4679_, 0);
                    crate::leanh::lean_inc_ref(v_env_4680_);
                    crate::leanh::lean_dec(v___x_4679_);
                    v___x_4681_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
                    v_toEnvExtension_4682_ = crate::leanh::lean_ctor_get(v___x_4681_, 0);
                    v_asyncMode_4683_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4682_, 2);
                    v___x_4684_ = crate::leanh::lean_box(0);
                    v_a_4685_ = lean_array_uget_borrowed(v_as_4666_, v_i_4668_);
                    v___x_4686_ = l_Lean_TSyntax_getId(v_a_4685_);
                    v___x_4731_ = crate::leanh::lean_box(1);
                    v___x_4732_ = crate::leanh::lean_box(0);
                    v___x_4733_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_4731_,
                        v___x_4681_,
                        v_env_4680_,
                        v_asyncMode_4683_,
                        v___x_4732_,
                    );
                    v___x_4734_ = l_Lean_NameSet_contains(v___x_4733_, v___x_4686_);
                    crate::leanh::lean_dec(v___x_4733_);
                    if v___x_4734_ == 0 {
                        v___y_4688_ = v___y_4673_;
                        v___y_4689_ = v___y_4675_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4735_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
                        crate::leanh::lean_inc(v___x_4686_);
                        v___x_4736_ = l_Lean_MessageData_ofName(v___x_4686_);
                        v___x_4737_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4737_, 0, v___x_4735_);
                        crate::leanh::lean_ctor_set(v___x_4737_, 1, v___x_4736_);
                        v___x_4738_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1);
                        v___x_4739_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4739_, 0, v___x_4737_);
                        crate::leanh::lean_ctor_set(v___x_4739_, 1, v___x_4738_);
                        v___x_4740_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v___x_4739_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
                        if crate::leanh::lean_obj_tag(v___x_4740_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4740_, 1);
                            v___y_4688_ = v___y_4673_;
                            v___y_4689_ = v___y_4675_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4686_);
                            return v___x_4740_;
                        }
                    }
                }
            }
            1 => {
                v___x_4690_ = lean_st_ref_take(v___y_4689_);
                v_toEnvExtension_4691_ = crate::leanh::lean_ctor_get(v___x_4681_, 0);
                v_env_4692_ = crate::leanh::lean_ctor_get(v___x_4690_, 0);
                v_nextMacroScope_4693_ = crate::leanh::lean_ctor_get(v___x_4690_, 1);
                v_ngen_4694_ = crate::leanh::lean_ctor_get(v___x_4690_, 2);
                v_auxDeclNGen_4695_ = crate::leanh::lean_ctor_get(v___x_4690_, 3);
                v_traceState_4696_ = crate::leanh::lean_ctor_get(v___x_4690_, 4);
                v_messages_4697_ = crate::leanh::lean_ctor_get(v___x_4690_, 6);
                v_infoState_4698_ = crate::leanh::lean_ctor_get(v___x_4690_, 7);
                v_snapshotTasks_4699_ = crate::leanh::lean_ctor_get(v___x_4690_, 8);
                v_isSharedCheck_4729_ = (!crate::leanh::lean_is_exclusive(v___x_4690_)) as u8;
                if v_isSharedCheck_4729_ == 0 {
                    v_unused_4730_ = crate::leanh::lean_ctor_get(v___x_4690_, 5);
                    crate::leanh::lean_dec(v_unused_4730_);
                    v___x_4701_ = v___x_4690_;
                    v_isShared_4702_ = v_isSharedCheck_4729_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4699_);
                    crate::leanh::lean_inc(v_infoState_4698_);
                    crate::leanh::lean_inc(v_messages_4697_);
                    crate::leanh::lean_inc(v_traceState_4696_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4695_);
                    crate::leanh::lean_inc(v_ngen_4694_);
                    crate::leanh::lean_inc(v_nextMacroScope_4693_);
                    crate::leanh::lean_inc(v_env_4692_);
                    crate::leanh::lean_dec(v___x_4690_);
                    v___x_4701_ = crate::leanh::lean_box(0);
                    v_isShared_4702_ = v_isSharedCheck_4729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4703_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4691_, 2);
                v___x_4704_ = crate::leanh::lean_box(0);
                v___x_4705_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4681_,
                    v_env_4692_,
                    v___x_4686_,
                    v_asyncMode_4703_,
                    v___x_4704_,
                );
                v___x_4706_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2);
                if v_isShared_4702_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4701_, 5, v___x_4706_);
                    crate::leanh::lean_ctor_set(v___x_4701_, 0, v___x_4705_);
                    v___x_4708_ = v___x_4701_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4728_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 0, v___x_4705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 1, v_nextMacroScope_4693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 2, v_ngen_4694_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 3, v_auxDeclNGen_4695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 4, v_traceState_4696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 5, v___x_4706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 6, v_messages_4697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 7, v_infoState_4698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 8, v_snapshotTasks_4699_);
                    v___x_4708_ = v_reuseFailAlloc_4728_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4709_ = lean_st_ref_set(v___y_4689_, v___x_4708_);
                v___x_4710_ = lean_st_ref_take(v___y_4688_);
                v_mctx_4711_ = crate::leanh::lean_ctor_get(v___x_4710_, 0);
                v_zetaDeltaFVarIds_4712_ = crate::leanh::lean_ctor_get(v___x_4710_, 2);
                v_postponed_4713_ = crate::leanh::lean_ctor_get(v___x_4710_, 3);
                v_diag_4714_ = crate::leanh::lean_ctor_get(v___x_4710_, 4);
                v_isSharedCheck_4726_ = (!crate::leanh::lean_is_exclusive(v___x_4710_)) as u8;
                if v_isSharedCheck_4726_ == 0 {
                    v_unused_4727_ = crate::leanh::lean_ctor_get(v___x_4710_, 1);
                    crate::leanh::lean_dec(v_unused_4727_);
                    v___x_4716_ = v___x_4710_;
                    v_isShared_4717_ = v_isSharedCheck_4726_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4714_);
                    crate::leanh::lean_inc(v_postponed_4713_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4712_);
                    crate::leanh::lean_inc(v_mctx_4711_);
                    crate::leanh::lean_dec(v___x_4710_);
                    v___x_4716_ = crate::leanh::lean_box(0);
                    v_isShared_4717_ = v_isSharedCheck_4726_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4718_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3);
                if v_isShared_4717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4716_, 1, v___x_4718_);
                    v___x_4720_ = v___x_4716_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4725_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_mctx_4711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4725_, 1, v___x_4718_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4725_,
                        2,
                        v_zetaDeltaFVarIds_4712_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4725_, 3, v_postponed_4713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4725_, 4, v_diag_4714_);
                    v___x_4720_ = v_reuseFailAlloc_4725_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4721_ = lean_st_ref_set(v___y_4688_, v___x_4720_);
                v___x_4722_ = 1usize;
                v___x_4723_ = lean_usize_add(v_i_4668_, v___x_4722_);
                v_i_4668_ = v___x_4723_;
                v_b_4669_ = v___x_4684_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___boxed(
    mut v_as_4741_: *mut crate::leanh::LeanObject,
    mut v_sz_4742_: *mut crate::leanh::LeanObject,
    mut v_i_4743_: *mut crate::leanh::LeanObject,
    mut v_b_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
    mut v___y_4746_: *mut crate::leanh::LeanObject,
    mut v___y_4747_: *mut crate::leanh::LeanObject,
    mut v___y_4748_: *mut crate::leanh::LeanObject,
    mut v___y_4749_: *mut crate::leanh::LeanObject,
    mut v___y_4750_: *mut crate::leanh::LeanObject,
    mut v___y_4751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4752_: usize = 0;
    let mut v_i_boxed_4753_: usize = 0;
    let mut v_res_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4752_ = crate::leanh::lean_unbox_usize(v_sz_4742_);
    crate::leanh::lean_dec(v_sz_4742_);
    v_i_boxed_4753_ = crate::leanh::lean_unbox_usize(v_i_4743_);
    crate::leanh::lean_dec(v_i_4743_);
    v_res_4754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(v_as_4741_, v_sz_boxed_4752_, v_i_boxed_4753_, v_b_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
    crate::leanh::lean_dec(v___y_4750_);
    crate::leanh::lean_dec_ref(v___y_4749_);
    crate::leanh::lean_dec(v___y_4748_);
    crate::leanh::lean_dec_ref(v___y_4747_);
    crate::leanh::lean_dec(v___y_4746_);
    crate::leanh::lean_dec_ref(v___y_4745_);
    crate::leanh::lean_dec_ref(v_as_4741_);
    return v_res_4754_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0(
    mut v___y_4755_: u8,
    mut v_ids_4756_: *mut crate::leanh::LeanObject,
    mut v___y_4757_: *mut crate::leanh::LeanObject,
    mut v___y_4758_: *mut crate::leanh::LeanObject,
    mut v___y_4759_: *mut crate::leanh::LeanObject,
    mut v___y_4760_: *mut crate::leanh::LeanObject,
    mut v___y_4761_: *mut crate::leanh::LeanObject,
    mut v___y_4762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4765_: usize = 0;
    let mut v___x_4766_: usize = 0;
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4770_: u8 = 0;
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4774_: u8 = 0;
    let mut v_unused_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4777_: usize = 0;
    let mut v___x_4778_: usize = 0;
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4782_: u8 = 0;
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4786_: u8 = 0;
    let mut v_unused_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_4755_ == 0 {
                    v___x_4764_ = crate::leanh::lean_box(0);
                    v_sz_4765_ = lean_array_size(v_ids_4756_);
                    v___x_4766_ = 0usize;
                    v___x_4767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(v_ids_4756_, v_sz_4765_, v___x_4766_, v___x_4764_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_);
                    if crate::leanh::lean_obj_tag(v___x_4767_) == 0 {
                        v_isSharedCheck_4774_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4767_)) as u8;
                        if v_isSharedCheck_4774_ == 0 {
                            v_unused_4775_ = crate::leanh::lean_ctor_get(v___x_4767_, 0);
                            crate::leanh::lean_dec(v_unused_4775_);
                            v___x_4769_ = v___x_4767_;
                            v_isShared_4770_ = v_isSharedCheck_4774_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4767_);
                            v___x_4769_ = crate::leanh::lean_box(0);
                            v_isShared_4770_ = v_isSharedCheck_4774_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_4767_;
                    }
                } else {
                    v___x_4776_ = crate::leanh::lean_box(0);
                    v_sz_4777_ = lean_array_size(v_ids_4756_);
                    v___x_4778_ = 0usize;
                    v___x_4779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(v_ids_4756_, v_sz_4777_, v___x_4778_, v___x_4776_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_);
                    if crate::leanh::lean_obj_tag(v___x_4779_) == 0 {
                        v_isSharedCheck_4786_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4779_)) as u8;
                        if v_isSharedCheck_4786_ == 0 {
                            v_unused_4787_ = crate::leanh::lean_ctor_get(v___x_4779_, 0);
                            crate::leanh::lean_dec(v_unused_4787_);
                            v___x_4781_ = v___x_4779_;
                            v_isShared_4782_ = v_isSharedCheck_4786_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4779_);
                            v___x_4781_ = crate::leanh::lean_box(0);
                            v_isShared_4782_ = v_isSharedCheck_4786_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_4779_;
                    }
                }
            }
            1 => {
                if v_isShared_4770_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4769_, 0, v___x_4764_);
                    v___x_4772_ = v___x_4769_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4773_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4764_);
                    v___x_4772_ = v_reuseFailAlloc_4773_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4772_;
            }
            3 => {
                if v_isShared_4782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4781_, 0, v___x_4776_);
                    v___x_4784_ = v___x_4781_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4785_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4776_);
                    v___x_4784_ = v_reuseFailAlloc_4785_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0___boxed(
    mut v___y_4788_: *mut crate::leanh::LeanObject,
    mut v_ids_4789_: *mut crate::leanh::LeanObject,
    mut v___y_4790_: *mut crate::leanh::LeanObject,
    mut v___y_4791_: *mut crate::leanh::LeanObject,
    mut v___y_4792_: *mut crate::leanh::LeanObject,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
    mut v___y_4794_: *mut crate::leanh::LeanObject,
    mut v___y_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_8781__boxed_4797_: u8 = 0;
    let mut v_res_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_8781__boxed_4797_ = (crate::leanh::lean_unbox(v___y_4788_) as u8);
    v_res_4798_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0(v___y_8781__boxed_4797_, v_ids_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
    crate::leanh::lean_dec(v___y_4795_);
    crate::leanh::lean_dec_ref(v___y_4794_);
    crate::leanh::lean_dec(v___y_4793_);
    crate::leanh::lean_dec_ref(v___y_4792_);
    crate::leanh::lean_dec(v___y_4791_);
    crate::leanh::lean_dec_ref(v___y_4790_);
    crate::leanh::lean_dec_ref(v_ids_4789_);
    return v_res_4798_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip(
    mut v_stx_4804_: *mut crate::leanh::LeanObject,
    mut v_a_4805_: *mut crate::leanh::LeanObject,
    mut v_a_4806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4812_: u8 = 0;
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: u8 = 0;
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: u8 = 0;
    let mut v_sfx_x3f_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: u8 = 0;
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: u8 = 0;
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sfx_x3f_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4821_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1;
                crate::leanh::lean_inc(v_stx_4804_);
                v___x_4822_ = l_Lean_Syntax_isOfKind(v_stx_4804_, v___x_4821_);
                if v___x_4822_ == 0 {
                    crate::leanh::lean_dec(v_stx_4804_);
                    v___x_4830_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
                    return v___x_4830_;
                } else {
                    v___x_4831_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_4832_ = l_Lean_Syntax_getArg(v_stx_4804_, v___x_4831_);
                    v___x_4833_ = l_Lean_Syntax_isNone(v___x_4832_);
                    if v___x_4833_ == 0 {
                        v___x_4834_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_4832_);
                        v___x_4835_ = l_Lean_Syntax_matchesNull(v___x_4832_, v___x_4834_);
                        if v___x_4835_ == 0 {
                            crate::leanh::lean_dec(v___x_4832_);
                            crate::leanh::lean_dec(v_stx_4804_);
                            v___x_4836_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
                            return v___x_4836_;
                        } else {
                            v___x_4837_ = crate::leanh::lean_unsigned_to_nat(0);
                            v_sfx_x3f_4838_ = l_Lean_Syntax_getArg(v___x_4832_, v___x_4837_);
                            crate::leanh::lean_dec(v___x_4832_);
                            v___x_4839_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4839_, 0, v_sfx_x3f_4838_);
                            v_sfx_x3f_4824_ = v___x_4839_;
                            v___y_4825_ = v_a_4805_;
                            v___y_4826_ = v_a_4806_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4832_);
                        v___x_4840_ = crate::leanh::lean_box(0);
                        v_sfx_x3f_4824_ = v___x_4840_;
                        v___y_4825_ = v_a_4805_;
                        v___y_4826_ = v_a_4806_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4813_ = crate::leanh::lean_box((v___y_4812_) as usize);
                v___y_4814_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                crate::leanh::lean_closure_set(v___y_4814_, 0, v___x_4813_);
                crate::leanh::lean_closure_set(v___y_4814_, 1, v___y_4809_);
                v___x_4815_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                    v___y_4814_,
                    v___y_4810_,
                    v___y_4811_,
                );
                return v___x_4815_;
            }
            2 => {
                v___x_4820_ = 0;
                v___y_4809_ = v___y_4818_;
                v___y_4810_ = v___y_4817_;
                v___y_4811_ = v___y_4819_;
                v___y_4812_ = v___x_4820_;
                state = 1;
                continue;
            }
            3 => {
                v___x_4827_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4828_ = l_Lean_Syntax_getArg(v_stx_4804_, v___x_4827_);
                crate::leanh::lean_dec(v_stx_4804_);
                v_ids_4829_ = l_Lean_Syntax_getArgs(v___x_4828_);
                crate::leanh::lean_dec(v___x_4828_);
                if crate::leanh::lean_obj_tag(v_sfx_x3f_4824_) == 0 {
                    v___y_4817_ = v___y_4825_;
                    v___y_4818_ = v_ids_4829_;
                    v___y_4819_ = v___y_4826_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_sfx_x3f_4824_, 1);
                    if v___x_4822_ == 0 {
                        v___y_4817_ = v___y_4825_;
                        v___y_4818_ = v_ids_4829_;
                        v___y_4819_ = v___y_4826_;
                        state = 2;
                        continue;
                    } else {
                        v___y_4809_ = v_ids_4829_;
                        v___y_4810_ = v___y_4825_;
                        v___y_4811_ = v___y_4826_;
                        v___y_4812_ = v___x_4822_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___boxed(
    mut v_stx_4841_: *mut crate::leanh::LeanObject,
    mut v_a_4842_: *mut crate::leanh::LeanObject,
    mut v_a_4843_: *mut crate::leanh::LeanObject,
    mut v_a_4844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4845_ =
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip(
            v_stx_4841_,
            v_a_4842_,
            v_a_4843_,
        );
    crate::leanh::lean_dec(v_a_4843_);
    crate::leanh::lean_dec_ref(v_a_4842_);
    return v_res_4845_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0(
    mut v_00_u03b1_4846_: *mut crate::leanh::LeanObject,
    mut v_msg_4847_: *mut crate::leanh::LeanObject,
    mut v___y_4848_: *mut crate::leanh::LeanObject,
    mut v___y_4849_: *mut crate::leanh::LeanObject,
    mut v___y_4850_: *mut crate::leanh::LeanObject,
    mut v___y_4851_: *mut crate::leanh::LeanObject,
    mut v___y_4852_: *mut crate::leanh::LeanObject,
    mut v___y_4853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4855_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v_msg_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_);
    return v___x_4855_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___boxed(
    mut v_00_u03b1_4856_: *mut crate::leanh::LeanObject,
    mut v_msg_4857_: *mut crate::leanh::LeanObject,
    mut v___y_4858_: *mut crate::leanh::LeanObject,
    mut v___y_4859_: *mut crate::leanh::LeanObject,
    mut v___y_4860_: *mut crate::leanh::LeanObject,
    mut v___y_4861_: *mut crate::leanh::LeanObject,
    mut v___y_4862_: *mut crate::leanh::LeanObject,
    mut v___y_4863_: *mut crate::leanh::LeanObject,
    mut v___y_4864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4865_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0(v_00_u03b1_4856_, v_msg_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
    crate::leanh::lean_dec(v___y_4863_);
    crate::leanh::lean_dec_ref(v___y_4862_);
    crate::leanh::lean_dec(v___y_4861_);
    crate::leanh::lean_dec_ref(v___y_4860_);
    crate::leanh::lean_dec(v___y_4859_);
    crate::leanh::lean_dec_ref(v___y_4858_);
    return v_res_4865_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1(
    mut v_msgData_4866_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4867_: *mut crate::leanh::LeanObject,
    mut v___y_4868_: *mut crate::leanh::LeanObject,
    mut v___y_4869_: *mut crate::leanh::LeanObject,
    mut v___y_4870_: *mut crate::leanh::LeanObject,
    mut v___y_4871_: *mut crate::leanh::LeanObject,
    mut v___y_4872_: *mut crate::leanh::LeanObject,
    mut v___y_4873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4875_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(v_msgData_4866_, v_macroStack_4867_, v___y_4872_);
    return v___x_4875_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___boxed(
    mut v_msgData_4876_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4877_: *mut crate::leanh::LeanObject,
    mut v___y_4878_: *mut crate::leanh::LeanObject,
    mut v___y_4879_: *mut crate::leanh::LeanObject,
    mut v___y_4880_: *mut crate::leanh::LeanObject,
    mut v___y_4881_: *mut crate::leanh::LeanObject,
    mut v___y_4882_: *mut crate::leanh::LeanObject,
    mut v___y_4883_: *mut crate::leanh::LeanObject,
    mut v___y_4884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4885_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1(v_msgData_4876_, v_macroStack_4877_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_);
    crate::leanh::lean_dec(v___y_4883_);
    crate::leanh::lean_dec_ref(v___y_4882_);
    crate::leanh::lean_dec(v___y_4881_);
    crate::leanh::lean_dec_ref(v___y_4880_);
    crate::leanh::lean_dec(v___y_4879_);
    crate::leanh::lean_dec_ref(v___y_4878_);
    return v_res_4885_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4891_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_4892_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1;
    v___x_4893_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__1;
    v___x_4894_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___boxed
            as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_4895_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4891_,
        v___x_4892_,
        v___x_4893_,
        v___x_4894_,
    );
    return v___x_4895_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___boxed(
    mut v_a_4896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4897_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1();
    return v_res_4897_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__0;
    v___x_4900_ = l_Lean_stringToMessageData(v___x_4899_);
    return v___x_4900_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(
    mut v_as_4901_: *mut crate::leanh::LeanObject,
    mut v_sz_4902_: usize,
    mut v_i_4903_: usize,
    mut v_b_4904_: *mut crate::leanh::LeanObject,
    mut v___y_4905_: *mut crate::leanh::LeanObject,
    mut v___y_4906_: *mut crate::leanh::LeanObject,
    mut v___y_4907_: *mut crate::leanh::LeanObject,
    mut v___y_4908_: *mut crate::leanh::LeanObject,
    mut v___y_4909_: *mut crate::leanh::LeanObject,
    mut v___y_4910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4912_: u8 = 0;
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4940_: u8 = 0;
    let mut v_asyncMode_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4955_: u8 = 0;
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: usize = 0;
    let mut v___x_4961_: usize = 0;
    let mut v_reuseFailAlloc_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4964_: u8 = 0;
    let mut v_unused_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4967_: u8 = 0;
    let mut v_unused_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: u8 = 0;
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4982_: u8 = 0;
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4912_ = lean_usize_dec_lt(v_i_4903_, v_sz_4902_);
                if v___x_4912_ == 0 {
                    v___x_4913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4913_, 0, v_b_4904_);
                    return v___x_4913_;
                } else {
                    v_a_4914_ = lean_array_uget_borrowed(v_as_4901_, v_i_4903_);
                    v___x_4915_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_4914_);
                    v___x_4916_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                        v_a_4914_,
                        v___x_4915_,
                        v___y_4909_,
                        v___y_4910_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4916_) == 0 {
                        v_a_4917_ = crate::leanh::lean_ctor_get(v___x_4916_, 0);
                        crate::leanh::lean_inc_n(v_a_4917_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4916_, 1);
                        v___x_4918_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_a_4917_, v___y_4909_, v___y_4910_);
                        if crate::leanh::lean_obj_tag(v___x_4918_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4918_, 1);
                            v___x_4919_ = lean_st_ref_get(v___y_4910_);
                            v_env_4920_ = crate::leanh::lean_ctor_get(v___x_4919_, 0);
                            crate::leanh::lean_inc_ref(v_env_4920_);
                            crate::leanh::lean_dec(v___x_4919_);
                            v___x_4921_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
                            v_toEnvExtension_4922_ = crate::leanh::lean_ctor_get(v___x_4921_, 0);
                            v_asyncMode_4923_ =
                                crate::leanh::lean_ctor_get(v_toEnvExtension_4922_, 2);
                            v___x_4924_ = crate::leanh::lean_box(0);
                            v___x_4969_ = crate::leanh::lean_box(1);
                            v___x_4970_ = crate::leanh::lean_box(0);
                            v___x_4971_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                                v___x_4969_,
                                v___x_4921_,
                                v_env_4920_,
                                v_asyncMode_4923_,
                                v___x_4970_,
                            );
                            v___x_4972_ = l_Lean_NameSet_contains(v___x_4971_, v_a_4917_);
                            crate::leanh::lean_dec(v___x_4971_);
                            if v___x_4972_ == 0 {
                                v___y_4926_ = v___y_4908_;
                                v___y_4927_ = v___y_4910_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4973_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
                                crate::leanh::lean_inc(v_a_4917_);
                                v___x_4974_ = l_Lean_MessageData_ofName(v_a_4917_);
                                v___x_4975_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4975_, 0, v___x_4973_);
                                crate::leanh::lean_ctor_set(v___x_4975_, 1, v___x_4974_);
                                v___x_4976_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1);
                                v___x_4977_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4977_, 0, v___x_4975_);
                                crate::leanh::lean_ctor_set(v___x_4977_, 1, v___x_4976_);
                                v___x_4978_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v___x_4977_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_);
                                if crate::leanh::lean_obj_tag(v___x_4978_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4978_, 1);
                                    v___y_4926_ = v___y_4908_;
                                    v___y_4927_ = v___y_4910_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_4917_);
                                    return v___x_4978_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4917_);
                            return v___x_4918_;
                        }
                    } else {
                        v_a_4979_ = crate::leanh::lean_ctor_get(v___x_4916_, 0);
                        v_isSharedCheck_4986_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4916_)) as u8;
                        if v_isSharedCheck_4986_ == 0 {
                            v___x_4981_ = v___x_4916_;
                            v_isShared_4982_ = v_isSharedCheck_4986_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4979_);
                            crate::leanh::lean_dec(v___x_4916_);
                            v___x_4981_ = crate::leanh::lean_box(0);
                            v_isShared_4982_ = v_isSharedCheck_4986_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4928_ = lean_st_ref_take(v___y_4927_);
                v_toEnvExtension_4929_ = crate::leanh::lean_ctor_get(v___x_4921_, 0);
                v_env_4930_ = crate::leanh::lean_ctor_get(v___x_4928_, 0);
                v_nextMacroScope_4931_ = crate::leanh::lean_ctor_get(v___x_4928_, 1);
                v_ngen_4932_ = crate::leanh::lean_ctor_get(v___x_4928_, 2);
                v_auxDeclNGen_4933_ = crate::leanh::lean_ctor_get(v___x_4928_, 3);
                v_traceState_4934_ = crate::leanh::lean_ctor_get(v___x_4928_, 4);
                v_messages_4935_ = crate::leanh::lean_ctor_get(v___x_4928_, 6);
                v_infoState_4936_ = crate::leanh::lean_ctor_get(v___x_4928_, 7);
                v_snapshotTasks_4937_ = crate::leanh::lean_ctor_get(v___x_4928_, 8);
                v_isSharedCheck_4967_ = (!crate::leanh::lean_is_exclusive(v___x_4928_)) as u8;
                if v_isSharedCheck_4967_ == 0 {
                    v_unused_4968_ = crate::leanh::lean_ctor_get(v___x_4928_, 5);
                    crate::leanh::lean_dec(v_unused_4968_);
                    v___x_4939_ = v___x_4928_;
                    v_isShared_4940_ = v_isSharedCheck_4967_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4937_);
                    crate::leanh::lean_inc(v_infoState_4936_);
                    crate::leanh::lean_inc(v_messages_4935_);
                    crate::leanh::lean_inc(v_traceState_4934_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4933_);
                    crate::leanh::lean_inc(v_ngen_4932_);
                    crate::leanh::lean_inc(v_nextMacroScope_4931_);
                    crate::leanh::lean_inc(v_env_4930_);
                    crate::leanh::lean_dec(v___x_4928_);
                    v___x_4939_ = crate::leanh::lean_box(0);
                    v_isShared_4940_ = v_isSharedCheck_4967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4941_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4929_, 2);
                v___x_4942_ = crate::leanh::lean_box(0);
                v___x_4943_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4921_,
                    v_env_4930_,
                    v_a_4917_,
                    v_asyncMode_4941_,
                    v___x_4942_,
                );
                v___x_4944_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2);
                if v_isShared_4940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4939_, 5, v___x_4944_);
                    crate::leanh::lean_ctor_set(v___x_4939_, 0, v___x_4943_);
                    v___x_4946_ = v___x_4939_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4966_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4966_, 1, v_nextMacroScope_4931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4966_, 2, v_ngen_4932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4966_, 3, v_auxDeclNGen_4933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4966_, 4, v_traceState_4934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4966_, 5, v___x_4944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4966_, 6, v_messages_4935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4966_, 7, v_infoState_4936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4966_, 8, v_snapshotTasks_4937_);
                    v___x_4946_ = v_reuseFailAlloc_4966_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4947_ = lean_st_ref_set(v___y_4927_, v___x_4946_);
                v___x_4948_ = lean_st_ref_take(v___y_4926_);
                v_mctx_4949_ = crate::leanh::lean_ctor_get(v___x_4948_, 0);
                v_zetaDeltaFVarIds_4950_ = crate::leanh::lean_ctor_get(v___x_4948_, 2);
                v_postponed_4951_ = crate::leanh::lean_ctor_get(v___x_4948_, 3);
                v_diag_4952_ = crate::leanh::lean_ctor_get(v___x_4948_, 4);
                v_isSharedCheck_4964_ = (!crate::leanh::lean_is_exclusive(v___x_4948_)) as u8;
                if v_isSharedCheck_4964_ == 0 {
                    v_unused_4965_ = crate::leanh::lean_ctor_get(v___x_4948_, 1);
                    crate::leanh::lean_dec(v_unused_4965_);
                    v___x_4954_ = v___x_4948_;
                    v_isShared_4955_ = v_isSharedCheck_4964_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4952_);
                    crate::leanh::lean_inc(v_postponed_4951_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4950_);
                    crate::leanh::lean_inc(v_mctx_4949_);
                    crate::leanh::lean_dec(v___x_4948_);
                    v___x_4954_ = crate::leanh::lean_box(0);
                    v_isShared_4955_ = v_isSharedCheck_4964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4956_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3);
                if v_isShared_4955_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4954_, 1, v___x_4956_);
                    v___x_4958_ = v___x_4954_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4963_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_mctx_4949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 1, v___x_4956_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4963_,
                        2,
                        v_zetaDeltaFVarIds_4950_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 3, v_postponed_4951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 4, v_diag_4952_);
                    v___x_4958_ = v_reuseFailAlloc_4963_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4959_ = lean_st_ref_set(v___y_4926_, v___x_4958_);
                v___x_4960_ = 1usize;
                v___x_4961_ = lean_usize_add(v_i_4903_, v___x_4960_);
                v_i_4903_ = v___x_4961_;
                v_b_4904_ = v___x_4924_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_4982_ == 0 {
                    v___x_4984_ = v___x_4981_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4985_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4985_, 0, v_a_4979_);
                    v___x_4984_ = v_reuseFailAlloc_4985_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___boxed(
    mut v_as_4987_: *mut crate::leanh::LeanObject,
    mut v_sz_4988_: *mut crate::leanh::LeanObject,
    mut v_i_4989_: *mut crate::leanh::LeanObject,
    mut v_b_4990_: *mut crate::leanh::LeanObject,
    mut v___y_4991_: *mut crate::leanh::LeanObject,
    mut v___y_4992_: *mut crate::leanh::LeanObject,
    mut v___y_4993_: *mut crate::leanh::LeanObject,
    mut v___y_4994_: *mut crate::leanh::LeanObject,
    mut v___y_4995_: *mut crate::leanh::LeanObject,
    mut v___y_4996_: *mut crate::leanh::LeanObject,
    mut v___y_4997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4998_: usize = 0;
    let mut v_i_boxed_4999_: usize = 0;
    let mut v_res_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4998_ = crate::leanh::lean_unbox_usize(v_sz_4988_);
    crate::leanh::lean_dec(v_sz_4988_);
    v_i_boxed_4999_ = crate::leanh::lean_unbox_usize(v_i_4989_);
    crate::leanh::lean_dec(v_i_4989_);
    v_res_5000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(v_as_4987_, v_sz_boxed_4998_, v_i_boxed_4999_, v_b_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
    crate::leanh::lean_dec(v___y_4996_);
    crate::leanh::lean_dec_ref(v___y_4995_);
    crate::leanh::lean_dec(v___y_4994_);
    crate::leanh::lean_dec_ref(v___y_4993_);
    crate::leanh::lean_dec(v___y_4992_);
    crate::leanh::lean_dec_ref(v___y_4991_);
    crate::leanh::lean_dec_ref(v_as_4987_);
    return v_res_5000_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0(
    mut v_ids_5001_: *mut crate::leanh::LeanObject,
    mut v_sz_5002_: usize,
    mut v___x_5003_: usize,
    mut v___x_5004_: *mut crate::leanh::LeanObject,
    mut v___y_5005_: *mut crate::leanh::LeanObject,
    mut v___y_5006_: *mut crate::leanh::LeanObject,
    mut v___y_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
    mut v___y_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5015_: u8 = 0;
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5019_: u8 = 0;
    let mut v_unused_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(v_ids_5001_, v_sz_5002_, v___x_5003_, v___x_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
                if crate::leanh::lean_obj_tag(v___x_5012_) == 0 {
                    v_isSharedCheck_5019_ = (!crate::leanh::lean_is_exclusive(v___x_5012_)) as u8;
                    if v_isSharedCheck_5019_ == 0 {
                        v_unused_5020_ = crate::leanh::lean_ctor_get(v___x_5012_, 0);
                        crate::leanh::lean_dec(v_unused_5020_);
                        v___x_5014_ = v___x_5012_;
                        v_isShared_5015_ = v_isSharedCheck_5019_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5012_);
                        v___x_5014_ = crate::leanh::lean_box(0);
                        v_isShared_5015_ = v_isSharedCheck_5019_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_5012_;
                }
            }
            1 => {
                if v_isShared_5015_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5014_, 0, v___x_5004_);
                    v___x_5017_ = v___x_5014_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5018_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5004_);
                    v___x_5017_ = v_reuseFailAlloc_5018_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0___boxed(
    mut v_ids_5021_: *mut crate::leanh::LeanObject,
    mut v_sz_5022_: *mut crate::leanh::LeanObject,
    mut v___x_5023_: *mut crate::leanh::LeanObject,
    mut v___x_5024_: *mut crate::leanh::LeanObject,
    mut v___y_5025_: *mut crate::leanh::LeanObject,
    mut v___y_5026_: *mut crate::leanh::LeanObject,
    mut v___y_5027_: *mut crate::leanh::LeanObject,
    mut v___y_5028_: *mut crate::leanh::LeanObject,
    mut v___y_5029_: *mut crate::leanh::LeanObject,
    mut v___y_5030_: *mut crate::leanh::LeanObject,
    mut v___y_5031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5032_: usize = 0;
    let mut v___x_3710__boxed_5033_: usize = 0;
    let mut v_res_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5032_ = crate::leanh::lean_unbox_usize(v_sz_5022_);
    crate::leanh::lean_dec(v_sz_5022_);
    v___x_3710__boxed_5033_ = crate::leanh::lean_unbox_usize(v___x_5023_);
    crate::leanh::lean_dec(v___x_5023_);
    v_res_5034_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0(v_ids_5021_, v_sz_boxed_5032_, v___x_3710__boxed_5033_, v___x_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
    crate::leanh::lean_dec(v___y_5030_);
    crate::leanh::lean_dec_ref(v___y_5029_);
    crate::leanh::lean_dec(v___y_5028_);
    crate::leanh::lean_dec_ref(v___y_5027_);
    crate::leanh::lean_dec(v___y_5026_);
    crate::leanh::lean_dec_ref(v___y_5025_);
    crate::leanh::lean_dec_ref(v_ids_5021_);
    return v_res_5034_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute(
    mut v_stx_5042_: *mut crate::leanh::LeanObject,
    mut v_a_5043_: *mut crate::leanh::LeanObject,
    mut v_a_5044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: u8 = 0;
    v___x_5046_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1;
    crate::leanh::lean_inc(v_stx_5042_);
    v___x_5047_ = l_Lean_Syntax_isOfKind(v_stx_5042_, v___x_5046_);
    if v___x_5047_ == 0 {
        let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_5042_);
        v___x_5048_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
        return v___x_5048_;
    } else {
        let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ids_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5053_: usize = 0;
        let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5049_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_5050_ = l_Lean_Syntax_getArg(v_stx_5042_, v___x_5049_);
        crate::leanh::lean_dec(v_stx_5042_);
        v_ids_5051_ = l_Lean_Syntax_getArgs(v___x_5050_);
        crate::leanh::lean_dec(v___x_5050_);
        v___x_5052_ = crate::leanh::lean_box(0);
        v_sz_5053_ = lean_array_size(v_ids_5051_);
        v___x_5054_ = crate::leanh::lean_box_usize(v_sz_5053_);
        v___x_5055_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed__const__1;
        v___f_5056_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0___boxed as *mut core::ffi::c_void, 11, 4);
        crate::leanh::lean_closure_set(v___f_5056_, 0, v_ids_5051_);
        crate::leanh::lean_closure_set(v___f_5056_, 1, v___x_5054_);
        crate::leanh::lean_closure_set(v___f_5056_, 2, v___x_5055_);
        crate::leanh::lean_closure_set(v___f_5056_, 3, v___x_5052_);
        v___x_5057_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_5056_, v_a_5043_, v_a_5044_);
        return v___x_5057_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed(
    mut v_stx_5058_: *mut crate::leanh::LeanObject,
    mut v_a_5059_: *mut crate::leanh::LeanObject,
    mut v_a_5060_: *mut crate::leanh::LeanObject,
    mut v_a_5061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5062_ =
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute(
            v_stx_5058_,
            v_a_5059_,
            v_a_5060_,
        );
    crate::leanh::lean_dec(v_a_5060_);
    crate::leanh::lean_dec_ref(v_a_5059_);
    return v_res_5062_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5068_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_5069_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1;
    v___x_5070_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__1;
    v___x_5071_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed
            as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_5072_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5068_,
        v___x_5069_,
        v___x_5070_,
        v___x_5071_,
    );
    return v___x_5072_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___boxed(
    mut v_a_5073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5074_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1();
    return v_res_5074_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(
    mut v_items_5090_: *mut crate::leanh::LeanObject,
    mut v_a_5091_: *mut crate::leanh::LeanObject,
    mut v_a_5092_: *mut crate::leanh::LeanObject,
    mut v_a_5093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5095_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig;
    v___x_5096_ = l_Lean_Elab_Tactic_Grind_elabConfigItems___redArg(
        v___x_5095_,
        v_items_5090_,
        v_a_5091_,
        v_a_5092_,
        v_a_5093_,
    );
    return v___x_5096_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg___boxed(
    mut v_items_5097_: *mut crate::leanh::LeanObject,
    mut v_a_5098_: *mut crate::leanh::LeanObject,
    mut v_a_5099_: *mut crate::leanh::LeanObject,
    mut v_a_5100_: *mut crate::leanh::LeanObject,
    mut v_a_5101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5102_ =
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(
            v_items_5097_,
            v_a_5098_,
            v_a_5099_,
            v_a_5100_,
        );
    crate::leanh::lean_dec(v_a_5100_);
    crate::leanh::lean_dec_ref(v_a_5099_);
    crate::leanh::lean_dec_ref(v_a_5098_);
    return v_res_5102_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(
    mut v_items_5103_: *mut crate::leanh::LeanObject,
    mut v_a_5104_: *mut crate::leanh::LeanObject,
    mut v_a_5105_: *mut crate::leanh::LeanObject,
    mut v_a_5106_: *mut crate::leanh::LeanObject,
    mut v_a_5107_: *mut crate::leanh::LeanObject,
    mut v_a_5108_: *mut crate::leanh::LeanObject,
    mut v_a_5109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5111_ =
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(
            v_items_5103_,
            v_a_5104_,
            v_a_5108_,
            v_a_5109_,
        );
    return v___x_5111_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___boxed(
    mut v_items_5112_: *mut crate::leanh::LeanObject,
    mut v_a_5113_: *mut crate::leanh::LeanObject,
    mut v_a_5114_: *mut crate::leanh::LeanObject,
    mut v_a_5115_: *mut crate::leanh::LeanObject,
    mut v_a_5116_: *mut crate::leanh::LeanObject,
    mut v_a_5117_: *mut crate::leanh::LeanObject,
    mut v_a_5118_: *mut crate::leanh::LeanObject,
    mut v_a_5119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5120_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(
        v_items_5112_,
        v_a_5113_,
        v_a_5114_,
        v_a_5115_,
        v_a_5116_,
        v_a_5117_,
        v_a_5118_,
    );
    crate::leanh::lean_dec(v_a_5118_);
    crate::leanh::lean_dec_ref(v_a_5117_);
    crate::leanh::lean_dec(v_a_5116_);
    crate::leanh::lean_dec_ref(v_a_5115_);
    crate::leanh::lean_dec(v_a_5114_);
    crate::leanh::lean_dec_ref(v_a_5113_);
    return v_res_5120_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(
    mut v_init_5121_: *mut crate::leanh::LeanObject,
    mut v_x_5122_: *mut crate::leanh::LeanObject,
    mut v___y_5123_: *mut crate::leanh::LeanObject,
    mut v___y_5124_: *mut crate::leanh::LeanObject,
    mut v___y_5125_: *mut crate::leanh::LeanObject,
    mut v___y_5126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5140_: u8 = 0;
    let mut v___y_5142_: u8 = 0;
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: u8 = 0;
    let mut v___x_5148_: u8 = 0;
    let mut v_isSharedCheck_5149_: u8 = 0;
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5122_) == 0 {
                    v_k_5128_ = crate::leanh::lean_ctor_get(v_x_5122_, 1);
                    crate::leanh::lean_inc(v_k_5128_);
                    v_l_5129_ = crate::leanh::lean_ctor_get(v_x_5122_, 3);
                    crate::leanh::lean_inc(v_l_5129_);
                    v_r_5130_ = crate::leanh::lean_ctor_get(v_x_5122_, 4);
                    crate::leanh::lean_inc(v_r_5130_);
                    crate::leanh::lean_dec_ref_known(v_x_5122_, 5);
                    v___x_5131_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_init_5121_, v_l_5129_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
                    if crate::leanh::lean_obj_tag(v___x_5131_) == 0 {
                        v_a_5132_ = crate::leanh::lean_ctor_get(v___x_5131_, 0);
                        crate::leanh::lean_inc(v_a_5132_);
                        crate::leanh::lean_dec_ref_known(v___x_5131_, 1);
                        v_a_5133_ = crate::leanh::lean_ctor_get(v_a_5132_, 0);
                        crate::leanh::lean_inc_n(v_a_5133_, 2);
                        crate::leanh::lean_dec(v_a_5132_);
                        v___x_5134_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(
                            v_a_5133_,
                            v_k_5128_,
                            v___y_5123_,
                            v___y_5124_,
                            v___y_5125_,
                            v___y_5126_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5134_) == 0 {
                            crate::leanh::lean_dec(v_a_5133_);
                            v_a_5135_ = crate::leanh::lean_ctor_get(v___x_5134_, 0);
                            crate::leanh::lean_inc(v_a_5135_);
                            crate::leanh::lean_dec_ref_known(v___x_5134_, 1);
                            v_init_5121_ = v_a_5135_;
                            v_x_5122_ = v_r_5130_;
                            state = 0;
                            continue;
                        } else {
                            v_a_5137_ = crate::leanh::lean_ctor_get(v___x_5134_, 0);
                            v_isSharedCheck_5149_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5134_)) as u8;
                            if v_isSharedCheck_5149_ == 0 {
                                v___x_5139_ = v___x_5134_;
                                v_isShared_5140_ = v_isSharedCheck_5149_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5137_);
                                crate::leanh::lean_dec(v___x_5134_);
                                v___x_5139_ = crate::leanh::lean_box(0);
                                v_isShared_5140_ = v_isSharedCheck_5149_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_r_5130_);
                        crate::leanh::lean_dec(v_k_5128_);
                        return v___x_5131_;
                    }
                } else {
                    v___x_5150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5150_, 0, v_init_5121_);
                    v___x_5151_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5151_, 0, v___x_5150_);
                    return v___x_5151_;
                }
            }
            1 => {
                v___x_5147_ = l_Lean_Exception_isInterrupt(v_a_5137_);
                if v___x_5147_ == 0 {
                    crate::leanh::lean_inc(v_a_5137_);
                    v___x_5148_ = l_Lean_Exception_isRuntime(v_a_5137_);
                    v___y_5142_ = v___x_5148_;
                    state = 2;
                    continue;
                } else {
                    v___y_5142_ = v___x_5147_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_5142_ == 0 {
                    crate::leanh::lean_del_object(v___x_5139_);
                    crate::leanh::lean_dec(v_a_5137_);
                    v_init_5121_ = v_a_5133_;
                    v_x_5122_ = v_r_5130_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_5133_);
                    crate::leanh::lean_dec(v_r_5130_);
                    if v_isShared_5140_ == 0 {
                        v___x_5145_ = v___x_5139_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5146_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5137_);
                        v___x_5145_ = v_reuseFailAlloc_5146_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0___boxed(
    mut v_init_5152_: *mut crate::leanh::LeanObject,
    mut v_x_5153_: *mut crate::leanh::LeanObject,
    mut v___y_5154_: *mut crate::leanh::LeanObject,
    mut v___y_5155_: *mut crate::leanh::LeanObject,
    mut v___y_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: *mut crate::leanh::LeanObject,
    mut v___y_5158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5159_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_init_5152_, v_x_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_);
    crate::leanh::lean_dec(v___y_5157_);
    crate::leanh::lean_dec_ref(v___y_5156_);
    crate::leanh::lean_dec(v___y_5155_);
    crate::leanh::lean_dec_ref(v___y_5154_);
    return v_res_5159_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(
    mut v_config_5160_: *mut crate::leanh::LeanObject,
    mut v_a_5161_: *mut crate::leanh::LeanObject,
    mut v_a_5162_: *mut crate::leanh::LeanObject,
    mut v_a_5163_: *mut crate::leanh::LeanObject,
    mut v_a_5164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5170_: u8 = 0;
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extra_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraInj_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraFacts_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_symPrios_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_norm_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_normProcs_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchorRefs_x3f_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5183_: u8 = 0;
    let mut v___y_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: u8 = 0;
    let mut v_v_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_casesTypes_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funCC_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5216_: u8 = 0;
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5223_: u8 = 0;
    let mut v_unused_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5229_: u8 = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5233_: u8 = 0;
    let mut v_isSharedCheck_5234_: u8 = 0;
    let mut v_isSharedCheck_5235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5166_ = l_Lean_Meta_Grind_mkDefaultParams(
                    v_config_5160_,
                    v_a_5161_,
                    v_a_5162_,
                    v_a_5163_,
                    v_a_5164_,
                );
                if crate::leanh::lean_obj_tag(v___x_5166_) == 0 {
                    v_a_5167_ = crate::leanh::lean_ctor_get(v___x_5166_, 0);
                    v_isSharedCheck_5235_ = (!crate::leanh::lean_is_exclusive(v___x_5166_)) as u8;
                    if v_isSharedCheck_5235_ == 0 {
                        v___x_5169_ = v___x_5166_;
                        v_isShared_5170_ = v_isSharedCheck_5235_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5167_);
                        crate::leanh::lean_dec(v___x_5166_);
                        v___x_5169_ = crate::leanh::lean_box(0);
                        v_isShared_5170_ = v_isSharedCheck_5235_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_5166_;
                }
            }
            1 => {
                v___x_5171_ = lean_st_ref_get(v_a_5164_);
                v_config_5172_ = crate::leanh::lean_ctor_get(v_a_5167_, 0);
                v_extensions_5173_ = crate::leanh::lean_ctor_get(v_a_5167_, 1);
                v_extra_5174_ = crate::leanh::lean_ctor_get(v_a_5167_, 2);
                v_extraInj_5175_ = crate::leanh::lean_ctor_get(v_a_5167_, 3);
                v_extraFacts_5176_ = crate::leanh::lean_ctor_get(v_a_5167_, 4);
                v_symPrios_5177_ = crate::leanh::lean_ctor_get(v_a_5167_, 5);
                v_norm_5178_ = crate::leanh::lean_ctor_get(v_a_5167_, 6);
                v_normProcs_5179_ = crate::leanh::lean_ctor_get(v_a_5167_, 7);
                v_anchorRefs_x3f_5180_ = crate::leanh::lean_ctor_get(v_a_5167_, 8);
                v_isSharedCheck_5234_ = (!crate::leanh::lean_is_exclusive(v_a_5167_)) as u8;
                if v_isSharedCheck_5234_ == 0 {
                    v___x_5182_ = v_a_5167_;
                    v_isShared_5183_ = v_isSharedCheck_5234_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_anchorRefs_x3f_5180_);
                    crate::leanh::lean_inc(v_normProcs_5179_);
                    crate::leanh::lean_inc(v_norm_5178_);
                    crate::leanh::lean_inc(v_symPrios_5177_);
                    crate::leanh::lean_inc(v_extraFacts_5176_);
                    crate::leanh::lean_inc(v_extraInj_5175_);
                    crate::leanh::lean_inc(v_extra_5174_);
                    crate::leanh::lean_inc(v_extensions_5173_);
                    crate::leanh::lean_inc(v_config_5172_);
                    crate::leanh::lean_dec(v_a_5167_);
                    v___x_5182_ = crate::leanh::lean_box(0);
                    v_isShared_5183_ = v_isSharedCheck_5234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5192_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
                v___x_5193_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5194_ = lean_array_get_borrowed(v___x_5192_, v_extensions_5173_, v___x_5193_);
                v_ematch_5195_ = crate::leanh::lean_ctor_get(v___x_5194_, 3);
                v_env_5196_ = crate::leanh::lean_ctor_get(v___x_5171_, 0);
                crate::leanh::lean_inc_ref(v_env_5196_);
                crate::leanh::lean_dec(v___x_5171_);
                v___x_5197_ =
                    l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
                v_toEnvExtension_5198_ = crate::leanh::lean_ctor_get(v___x_5197_, 0);
                v_asyncMode_5199_ = crate::leanh::lean_ctor_get(v_toEnvExtension_5198_, 2);
                v___x_5200_ = crate::leanh::lean_box(1);
                v___x_5201_ = crate::leanh::lean_box(0);
                v___x_5202_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_5200_,
                    v___x_5197_,
                    v_env_5196_,
                    v_asyncMode_5199_,
                    v___x_5201_,
                );
                crate::leanh::lean_inc_ref(v_ematch_5195_);
                v___x_5203_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_ematch_5195_, v___x_5202_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
                if crate::leanh::lean_obj_tag(v___x_5203_) == 0 {
                    v_a_5204_ = crate::leanh::lean_ctor_get(v___x_5203_, 0);
                    crate::leanh::lean_inc(v_a_5204_);
                    crate::leanh::lean_dec_ref_known(v___x_5203_, 1);
                    v_a_5225_ = crate::leanh::lean_ctor_get(v_a_5204_, 0);
                    crate::leanh::lean_inc(v_a_5225_);
                    crate::leanh::lean_dec(v_a_5204_);
                    v_a_5206_ = v_a_5225_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_5182_);
                    crate::leanh::lean_dec(v_anchorRefs_x3f_5180_);
                    crate::leanh::lean_dec_ref(v_normProcs_5179_);
                    crate::leanh::lean_dec_ref(v_norm_5178_);
                    crate::leanh::lean_dec_ref(v_symPrios_5177_);
                    crate::leanh::lean_dec_ref(v_extraFacts_5176_);
                    crate::leanh::lean_dec_ref(v_extraInj_5175_);
                    crate::leanh::lean_dec_ref(v_extra_5174_);
                    crate::leanh::lean_dec_ref(v_extensions_5173_);
                    crate::leanh::lean_dec_ref(v_config_5172_);
                    crate::leanh::lean_del_object(v___x_5169_);
                    v_a_5226_ = crate::leanh::lean_ctor_get(v___x_5203_, 0);
                    v_isSharedCheck_5233_ = (!crate::leanh::lean_is_exclusive(v___x_5203_)) as u8;
                    if v_isSharedCheck_5233_ == 0 {
                        v___x_5228_ = v___x_5203_;
                        v_isShared_5229_ = v_isSharedCheck_5233_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5226_);
                        crate::leanh::lean_dec(v___x_5203_);
                        v___x_5228_ = crate::leanh::lean_box(0);
                        v_isShared_5229_ = v_isSharedCheck_5233_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5183_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5182_, 1, v___y_5185_);
                    v___x_5187_ = v___x_5182_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5191_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_config_5172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 1, v___y_5185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 2, v_extra_5174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 3, v_extraInj_5175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 4, v_extraFacts_5176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 5, v_symPrios_5177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 6, v_norm_5178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 7, v_normProcs_5179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 8, v_anchorRefs_x3f_5180_);
                    v___x_5187_ = v_reuseFailAlloc_5191_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5170_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5169_, 0, v___x_5187_);
                    v___x_5189_ = v___x_5169_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5190_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5190_, 0, v___x_5187_);
                    v___x_5189_ = v_reuseFailAlloc_5190_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5189_;
            }
            6 => {
                v___x_5207_ = lean_array_get_size(v_extensions_5173_);
                v___x_5208_ = lean_nat_dec_lt(v___x_5193_, v___x_5207_);
                if v___x_5208_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_5206_);
                    v___y_5185_ = v_extensions_5173_;
                    state = 3;
                    continue;
                } else {
                    v_v_5209_ = lean_array_fget(v_extensions_5173_, v___x_5193_);
                    v_casesTypes_5210_ = crate::leanh::lean_ctor_get(v_v_5209_, 0);
                    v_extThms_5211_ = crate::leanh::lean_ctor_get(v_v_5209_, 1);
                    v_funCC_5212_ = crate::leanh::lean_ctor_get(v_v_5209_, 2);
                    v_inj_5213_ = crate::leanh::lean_ctor_get(v_v_5209_, 4);
                    v_isSharedCheck_5223_ = (!crate::leanh::lean_is_exclusive(v_v_5209_)) as u8;
                    if v_isSharedCheck_5223_ == 0 {
                        v_unused_5224_ = crate::leanh::lean_ctor_get(v_v_5209_, 3);
                        crate::leanh::lean_dec(v_unused_5224_);
                        v___x_5215_ = v_v_5209_;
                        v_isShared_5216_ = v_isSharedCheck_5223_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_inj_5213_);
                        crate::leanh::lean_inc(v_funCC_5212_);
                        crate::leanh::lean_inc(v_extThms_5211_);
                        crate::leanh::lean_inc(v_casesTypes_5210_);
                        crate::leanh::lean_dec(v_v_5209_);
                        v___x_5215_ = crate::leanh::lean_box(0);
                        v_isShared_5216_ = v_isSharedCheck_5223_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_5217_ = crate::leanh::lean_box(0);
                v_xs_x27_5218_ = lean_array_fset(v_extensions_5173_, v___x_5193_, v___x_5217_);
                if v_isShared_5216_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5215_, 3, v_a_5206_);
                    v___x_5220_ = v___x_5215_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5222_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_casesTypes_5210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 1, v_extThms_5211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 2, v_funCC_5212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 3, v_a_5206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 4, v_inj_5213_);
                    v___x_5220_ = v_reuseFailAlloc_5222_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5221_ = lean_array_fset(v_xs_x27_5218_, v___x_5193_, v___x_5220_);
                v___y_5185_ = v___x_5221_;
                state = 3;
                continue;
            }
            9 => {
                if v_isShared_5229_ == 0 {
                    v___x_5231_ = v___x_5228_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
                    v___x_5231_ = v_reuseFailAlloc_5232_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams___boxed(
    mut v_config_5236_: *mut crate::leanh::LeanObject,
    mut v_a_5237_: *mut crate::leanh::LeanObject,
    mut v_a_5238_: *mut crate::leanh::LeanObject,
    mut v_a_5239_: *mut crate::leanh::LeanObject,
    mut v_a_5240_: *mut crate::leanh::LeanObject,
    mut v_a_5241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5242_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(
        v_config_5236_,
        v_a_5237_,
        v_a_5238_,
        v_a_5239_,
        v_a_5240_,
    );
    crate::leanh::lean_dec(v_a_5240_);
    crate::leanh::lean_dec_ref(v_a_5239_);
    crate::leanh::lean_dec(v_a_5238_);
    crate::leanh::lean_dec_ref(v_a_5237_);
    return v_res_5242_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0(
    mut v_x_5243_: *mut crate::leanh::LeanObject,
    mut v_____s_5244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_5245_ = crate::leanh::lean_ctor_get(v_x_5243_, 1);
    v_r_5246_ = lean_nat_add(v_____s_5244_, v_snd_5245_);
    v___x_5247_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5247_, 0, v_r_5246_);
    return v___x_5247_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0___boxed(
    mut v_x_5248_: *mut crate::leanh::LeanObject,
    mut v_____s_5249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5250_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0(
        v_x_5248_,
        v_____s_5249_,
    );
    crate::leanh::lean_dec(v_____s_5249_);
    crate::leanh::lean_dec_ref(v_x_5248_);
    return v_res_5250_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___lam__0(
    mut v_f_5251_: *mut crate::leanh::LeanObject,
    mut v_s_5252_: *mut crate::leanh::LeanObject,
    mut v_a_5253_: *mut crate::leanh::LeanObject,
    mut v_b_5254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5260_: u8 = 0;
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5264_: u8 = 0;
    let mut v_a_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5268_: u8 = 0;
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5255_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5255_, 0, v_a_5253_);
                crate::leanh::lean_ctor_set(v___x_5255_, 1, v_b_5254_);
                v___x_5256_ = crate::leanh::lean_apply_2(v_f_5251_, v___x_5255_, v_s_5252_);
                if crate::leanh::lean_obj_tag(v___x_5256_) == 0 {
                    v_a_5257_ = crate::leanh::lean_ctor_get(v___x_5256_, 0);
                    v_isSharedCheck_5264_ = (!crate::leanh::lean_is_exclusive(v___x_5256_)) as u8;
                    if v_isSharedCheck_5264_ == 0 {
                        v___x_5259_ = v___x_5256_;
                        v_isShared_5260_ = v_isSharedCheck_5264_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5257_);
                        crate::leanh::lean_dec(v___x_5256_);
                        v___x_5259_ = crate::leanh::lean_box(0);
                        v_isShared_5260_ = v_isSharedCheck_5264_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5265_ = crate::leanh::lean_ctor_get(v___x_5256_, 0);
                    v_isSharedCheck_5272_ = (!crate::leanh::lean_is_exclusive(v___x_5256_)) as u8;
                    if v_isSharedCheck_5272_ == 0 {
                        v___x_5267_ = v___x_5256_;
                        v_isShared_5268_ = v_isSharedCheck_5272_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5265_);
                        crate::leanh::lean_dec(v___x_5256_);
                        v___x_5267_ = crate::leanh::lean_box(0);
                        v_isShared_5268_ = v_isSharedCheck_5272_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5260_ == 0 {
                    v___x_5262_ = v___x_5259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_a_5257_);
                    v___x_5262_ = v_reuseFailAlloc_5263_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5262_;
            }
            3 => {
                if v_isShared_5268_ == 0 {
                    v___x_5270_ = v___x_5267_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5271_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5271_, 0, v_a_5265_);
                    v___x_5270_ = v_reuseFailAlloc_5271_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_f_5273_: *mut crate::leanh::LeanObject,
    mut v_keys_5274_: *mut crate::leanh::LeanObject,
    mut v_vals_5275_: *mut crate::leanh::LeanObject,
    mut v_i_5276_: *mut crate::leanh::LeanObject,
    mut v_acc_5277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: u8 = 0;
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5278_ = lean_array_get_size(v_keys_5274_);
                v___x_5279_ = lean_nat_dec_lt(v_i_5276_, v___x_5278_);
                if v___x_5279_ == 0 {
                    crate::leanh::lean_dec(v_i_5276_);
                    crate::leanh::lean_dec_ref(v_f_5273_);
                    v___x_5280_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5280_, 0, v_acc_5277_);
                    return v___x_5280_;
                } else {
                    v_k_5281_ = lean_array_fget_borrowed(v_keys_5274_, v_i_5276_);
                    v_v_5282_ = lean_array_fget_borrowed(v_vals_5275_, v_i_5276_);
                    crate::leanh::lean_inc_ref(v_f_5273_);
                    crate::leanh::lean_inc(v_v_5282_);
                    crate::leanh::lean_inc(v_k_5281_);
                    v___x_5283_ =
                        crate::leanh::lean_apply_3(v_f_5273_, v_acc_5277_, v_k_5281_, v_v_5282_);
                    if crate::leanh::lean_obj_tag(v___x_5283_) == 0 {
                        crate::leanh::lean_dec(v_i_5276_);
                        crate::leanh::lean_dec_ref(v_f_5273_);
                        return v___x_5283_;
                    } else {
                        v_a_5284_ = crate::leanh::lean_ctor_get(v___x_5283_, 0);
                        crate::leanh::lean_inc(v_a_5284_);
                        crate::leanh::lean_dec_ref_known(v___x_5283_, 1);
                        v___x_5285_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5286_ = lean_nat_add(v_i_5276_, v___x_5285_);
                        crate::leanh::lean_dec(v_i_5276_);
                        v_i_5276_ = v___x_5286_;
                        v_acc_5277_ = v_a_5284_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_f_5288_: *mut crate::leanh::LeanObject,
    mut v_keys_5289_: *mut crate::leanh::LeanObject,
    mut v_vals_5290_: *mut crate::leanh::LeanObject,
    mut v_i_5291_: *mut crate::leanh::LeanObject,
    mut v_acc_5292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5293_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_5288_, v_keys_5289_, v_vals_5290_, v_i_5291_, v_acc_5292_);
    crate::leanh::lean_dec_ref(v_vals_5290_);
    crate::leanh::lean_dec_ref(v_keys_5289_);
    return v_res_5293_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(
    mut v_f_5294_: *mut crate::leanh::LeanObject,
    mut v_x_5295_: *mut crate::leanh::LeanObject,
    mut v_x_5296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5300_: u8 = 0;
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: u8 = 0;
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: u8 = 0;
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: usize = 0;
    let mut v___x_5312_: usize = 0;
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: usize = 0;
    let mut v___x_5315_: usize = 0;
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut v_ks_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5295_) == 0 {
                    v_es_5297_ = crate::leanh::lean_ctor_get(v_x_5295_, 0);
                    v_isSharedCheck_5317_ = (!crate::leanh::lean_is_exclusive(v_x_5295_)) as u8;
                    if v_isSharedCheck_5317_ == 0 {
                        v___x_5299_ = v_x_5295_;
                        v_isShared_5300_ = v_isSharedCheck_5317_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_es_5297_);
                        crate::leanh::lean_dec(v_x_5295_);
                        v___x_5299_ = crate::leanh::lean_box(0);
                        v_isShared_5300_ = v_isSharedCheck_5317_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_5318_ = crate::leanh::lean_ctor_get(v_x_5295_, 0);
                    crate::leanh::lean_inc_ref(v_ks_5318_);
                    v_vs_5319_ = crate::leanh::lean_ctor_get(v_x_5295_, 1);
                    crate::leanh::lean_inc_ref(v_vs_5319_);
                    crate::leanh::lean_dec_ref_known(v_x_5295_, 2);
                    v___x_5320_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5321_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_5294_, v_ks_5318_, v_vs_5319_, v___x_5320_, v_x_5296_);
                    crate::leanh::lean_dec_ref(v_vs_5319_);
                    crate::leanh::lean_dec_ref(v_ks_5318_);
                    return v___x_5321_;
                }
            }
            1 => {
                v___x_5301_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5302_ = lean_array_get_size(v_es_5297_);
                v___x_5303_ = lean_nat_dec_lt(v___x_5301_, v___x_5302_);
                if v___x_5303_ == 0 {
                    crate::leanh::lean_dec_ref(v_es_5297_);
                    crate::leanh::lean_dec_ref(v_f_5294_);
                    if v_isShared_5300_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5299_, 1);
                        crate::leanh::lean_ctor_set(v___x_5299_, 0, v_x_5296_);
                        v___x_5305_ = v___x_5299_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5306_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_x_5296_);
                        v___x_5305_ = v_reuseFailAlloc_5306_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5307_ = lean_nat_dec_le(v___x_5302_, v___x_5302_);
                    if v___x_5307_ == 0 {
                        if v___x_5303_ == 0 {
                            crate::leanh::lean_dec_ref(v_es_5297_);
                            crate::leanh::lean_dec_ref(v_f_5294_);
                            if v_isShared_5300_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_5299_, 1);
                                crate::leanh::lean_ctor_set(v___x_5299_, 0, v_x_5296_);
                                v___x_5309_ = v___x_5299_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5310_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5310_, 0, v_x_5296_);
                                v___x_5309_ = v_reuseFailAlloc_5310_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5299_);
                            v___x_5311_ = 0usize;
                            v___x_5312_ = lean_usize_of_nat(v___x_5302_);
                            v___x_5313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_5294_, v_es_5297_, v___x_5311_, v___x_5312_, v_x_5296_);
                            crate::leanh::lean_dec_ref(v_es_5297_);
                            return v___x_5313_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5299_);
                        v___x_5314_ = 0usize;
                        v___x_5315_ = lean_usize_of_nat(v___x_5302_);
                        v___x_5316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_5294_, v_es_5297_, v___x_5314_, v___x_5315_, v_x_5296_);
                        crate::leanh::lean_dec_ref(v_es_5297_);
                        return v___x_5316_;
                    }
                }
            }
            2 => {
                return v___x_5305_;
            }
            3 => {
                return v___x_5309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_f_5322_: *mut crate::leanh::LeanObject,
    mut v_as_5323_: *mut crate::leanh::LeanObject,
    mut v_i_5324_: usize,
    mut v_stop_5325_: usize,
    mut v_b_5326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: usize = 0;
    let mut v___x_5330_: usize = 0;
    let mut v___y_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: u8 = 0;
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5335_ = lean_usize_dec_eq(v_i_5324_, v_stop_5325_);
                if v___x_5335_ == 0 {
                    v___x_5336_ = lean_array_uget_borrowed(v_as_5323_, v_i_5324_);
                    match crate::leanh::lean_obj_tag(v___x_5336_) {
                        0 => {
                            v_key_5337_ = crate::leanh::lean_ctor_get(v___x_5336_, 0);
                            v_val_5338_ = crate::leanh::lean_ctor_get(v___x_5336_, 1);
                            crate::leanh::lean_inc_ref(v_f_5322_);
                            crate::leanh::lean_inc(v_val_5338_);
                            crate::leanh::lean_inc(v_key_5337_);
                            v___x_5339_ = crate::leanh::lean_apply_3(
                                v_f_5322_,
                                v_b_5326_,
                                v_key_5337_,
                                v_val_5338_,
                            );
                            v___y_5333_ = v___x_5339_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_5340_ = crate::leanh::lean_ctor_get(v___x_5336_, 0);
                            crate::leanh::lean_inc(v_node_5340_);
                            crate::leanh::lean_inc_ref(v_f_5322_);
                            v___x_5341_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_5322_, v_node_5340_, v_b_5326_);
                            v___y_5333_ = v___x_5341_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_5328_ = v_b_5326_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5322_);
                    v___x_5342_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5342_, 0, v_b_5326_);
                    return v___x_5342_;
                }
            }
            1 => {
                v___x_5329_ = 1usize;
                v___x_5330_ = lean_usize_add(v_i_5324_, v___x_5329_);
                v_i_5324_ = v___x_5330_;
                v_b_5326_ = v_a_5328_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_5333_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_5322_);
                    return v___y_5333_;
                } else {
                    v_a_5334_ = crate::leanh::lean_ctor_get(v___y_5333_, 0);
                    crate::leanh::lean_inc(v_a_5334_);
                    crate::leanh::lean_dec_ref_known(v___y_5333_, 1);
                    v_a_5328_ = v_a_5334_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_f_5343_: *mut crate::leanh::LeanObject,
    mut v_as_5344_: *mut crate::leanh::LeanObject,
    mut v_i_5345_: *mut crate::leanh::LeanObject,
    mut v_stop_5346_: *mut crate::leanh::LeanObject,
    mut v_b_5347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5348_: usize = 0;
    let mut v_stop_boxed_5349_: usize = 0;
    let mut v_res_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5348_ = crate::leanh::lean_unbox_usize(v_i_5345_);
    crate::leanh::lean_dec(v_i_5345_);
    v_stop_boxed_5349_ = crate::leanh::lean_unbox_usize(v_stop_5346_);
    crate::leanh::lean_dec(v_stop_5346_);
    v_res_5350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_5343_, v_as_5344_, v_i_boxed_5348_, v_stop_boxed_5349_, v_b_5347_);
    crate::leanh::lean_dec_ref(v_as_5344_);
    return v_res_5350_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(
    mut v_map_5351_: *mut crate::leanh::LeanObject,
    mut v_init_5352_: *mut crate::leanh::LeanObject,
    mut v_f_5353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5354_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_5354_, 0, v_f_5353_);
    crate::leanh::lean_inc_ref(v_map_5351_);
    v___x_5355_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v___f_5354_, v_map_5351_, v_init_5352_);
    v_a_5356_ = crate::leanh::lean_ctor_get(v___x_5355_, 0);
    crate::leanh::lean_inc(v_a_5356_);
    crate::leanh::lean_dec_ref(v___x_5355_);
    return v_a_5356_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___boxed(
    mut v_map_5357_: *mut crate::leanh::LeanObject,
    mut v_init_5358_: *mut crate::leanh::LeanObject,
    mut v_f_5359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5360_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_map_5357_, v_init_5358_, v_f_5359_);
    crate::leanh::lean_dec_ref(v_map_5357_);
    return v_res_5360_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(
    mut v_cs_5362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5363_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___closed__0;
    v_r_5364_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5365_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_cs_5362_, v_r_5364_, v___f_5363_);
    return v___x_5365_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___boxed(
    mut v_cs_5366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5367_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(v_cs_5366_);
    crate::leanh::lean_dec_ref(v_cs_5366_);
    return v_res_5367_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0(
    mut v_00_u03c3_5368_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5369_: *mut crate::leanh::LeanObject,
    mut v_map_5370_: *mut crate::leanh::LeanObject,
    mut v_init_5371_: *mut crate::leanh::LeanObject,
    mut v_f_5372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5373_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_map_5370_, v_init_5371_, v_f_5372_);
    return v___x_5373_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___boxed(
    mut v_00_u03c3_5374_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5375_: *mut crate::leanh::LeanObject,
    mut v_map_5376_: *mut crate::leanh::LeanObject,
    mut v_init_5377_: *mut crate::leanh::LeanObject,
    mut v_f_5378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5379_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0(v_00_u03c3_5374_, v_00_u03b2_5375_, v_map_5376_, v_init_5377_, v_f_5378_);
    crate::leanh::lean_dec_ref(v_map_5376_);
    return v_res_5379_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0___redArg(
    mut v_map_5380_: *mut crate::leanh::LeanObject,
    mut v_f_5381_: *mut crate::leanh::LeanObject,
    mut v_init_5382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5383_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_5381_, v_map_5380_, v_init_5382_);
    return v___x_5383_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0(
    mut v_00_u03c3_5384_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5385_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5386_: *mut crate::leanh::LeanObject,
    mut v_map_5387_: *mut crate::leanh::LeanObject,
    mut v_f_5388_: *mut crate::leanh::LeanObject,
    mut v_init_5389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5390_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_5388_, v_map_5387_, v_init_5389_);
    return v___x_5390_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1(
    mut v_00_u03c3_5391_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5392_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5393_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5394_: *mut crate::leanh::LeanObject,
    mut v_f_5395_: *mut crate::leanh::LeanObject,
    mut v_x_5396_: *mut crate::leanh::LeanObject,
    mut v_x_5397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5398_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_5395_, v_x_5396_, v_x_5397_);
    return v___x_5398_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_5399_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5400_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5401_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5402_: *mut crate::leanh::LeanObject,
    mut v_f_5403_: *mut crate::leanh::LeanObject,
    mut v_as_5404_: *mut crate::leanh::LeanObject,
    mut v_i_5405_: usize,
    mut v_stop_5406_: usize,
    mut v_b_5407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_5403_, v_as_5404_, v_i_5405_, v_stop_5406_, v_b_5407_);
    return v___x_5408_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_5409_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5410_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5411_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5412_: *mut crate::leanh::LeanObject,
    mut v_f_5413_: *mut crate::leanh::LeanObject,
    mut v_as_5414_: *mut crate::leanh::LeanObject,
    mut v_i_5415_: *mut crate::leanh::LeanObject,
    mut v_stop_5416_: *mut crate::leanh::LeanObject,
    mut v_b_5417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5418_: usize = 0;
    let mut v_stop_boxed_5419_: usize = 0;
    let mut v_res_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5418_ = crate::leanh::lean_unbox_usize(v_i_5415_);
    crate::leanh::lean_dec(v_i_5415_);
    v_stop_boxed_5419_ = crate::leanh::lean_unbox_usize(v_stop_5416_);
    crate::leanh::lean_dec(v_stop_5416_);
    v_res_5420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_5409_, v_00_u03b2_5410_, v_00_u03c3_5411_, v_00_u03c3_5412_, v_f_5413_, v_as_5414_, v_i_boxed_5418_, v_stop_boxed_5419_, v_b_5417_);
    crate::leanh::lean_dec_ref(v_as_5414_);
    return v_res_5420_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03c3_5421_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5422_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5423_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5424_: *mut crate::leanh::LeanObject,
    mut v_f_5425_: *mut crate::leanh::LeanObject,
    mut v_keys_5426_: *mut crate::leanh::LeanObject,
    mut v_vals_5427_: *mut crate::leanh::LeanObject,
    mut v_heq_5428_: *mut crate::leanh::LeanObject,
    mut v_i_5429_: *mut crate::leanh::LeanObject,
    mut v_acc_5430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5431_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_5425_, v_keys_5426_, v_vals_5427_, v_i_5429_, v_acc_5430_);
    return v___x_5431_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03c3_5432_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5433_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5434_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5435_: *mut crate::leanh::LeanObject,
    mut v_f_5436_: *mut crate::leanh::LeanObject,
    mut v_keys_5437_: *mut crate::leanh::LeanObject,
    mut v_vals_5438_: *mut crate::leanh::LeanObject,
    mut v_heq_5439_: *mut crate::leanh::LeanObject,
    mut v_i_5440_: *mut crate::leanh::LeanObject,
    mut v_acc_5441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5442_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_5432_, v_00_u03c3_5433_, v_00_u03b1_5434_, v_00_u03b2_5435_, v_f_5436_, v_keys_5437_, v_vals_5438_, v_heq_5439_, v_i_5440_, v_acc_5441_);
    crate::leanh::lean_dec_ref(v_vals_5438_);
    crate::leanh::lean_dec_ref(v_keys_5437_);
    return v_res_5442_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(
    mut v_as_5443_: *mut crate::leanh::LeanObject,
    mut v_i_5444_: usize,
    mut v_stop_5445_: usize,
    mut v_b_5446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: usize = 0;
    let mut v___x_5450_: usize = 0;
    let mut v___x_5452_: u8 = 0;
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5458_: u8 = 0;
    let mut v_declName_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5464_: u8 = 0;
    let mut v_unused_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5452_ = lean_usize_dec_eq(v_i_5444_, v_stop_5445_);
                if v___x_5452_ == 0 {
                    v___x_5453_ = lean_array_uget(v_as_5443_, v_i_5444_);
                    v_fst_5454_ = crate::leanh::lean_ctor_get(v___x_5453_, 0);
                    crate::leanh::lean_inc(v_fst_5454_);
                    if crate::leanh::lean_obj_tag(v_fst_5454_) == 0 {
                        v_snd_5455_ = crate::leanh::lean_ctor_get(v___x_5453_, 1);
                        v_isSharedCheck_5464_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5453_)) as u8;
                        if v_isSharedCheck_5464_ == 0 {
                            v_unused_5465_ = crate::leanh::lean_ctor_get(v___x_5453_, 0);
                            crate::leanh::lean_dec(v_unused_5465_);
                            v___x_5457_ = v___x_5453_;
                            v_isShared_5458_ = v_isSharedCheck_5464_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_5455_);
                            crate::leanh::lean_dec(v___x_5453_);
                            v___x_5457_ = crate::leanh::lean_box(0);
                            v_isShared_5458_ = v_isSharedCheck_5464_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_5454_);
                        crate::leanh::lean_dec(v___x_5453_);
                        v___y_5448_ = v_b_5446_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5446_;
                }
            }
            1 => {
                v___x_5449_ = 1usize;
                v___x_5450_ = lean_usize_add(v_i_5444_, v___x_5449_);
                v_i_5444_ = v___x_5450_;
                v_b_5446_ = v___y_5448_;
                state = 0;
                continue;
            }
            2 => {
                v_declName_5459_ = crate::leanh::lean_ctor_get(v_fst_5454_, 0);
                crate::leanh::lean_inc(v_declName_5459_);
                crate::leanh::lean_dec_ref_known(v_fst_5454_, 1);
                if v_isShared_5458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5457_, 0, v_declName_5459_);
                    v___x_5461_ = v___x_5457_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5463_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5463_, 0, v_declName_5459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5463_, 1, v_snd_5455_);
                    v___x_5461_ = v_reuseFailAlloc_5463_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5462_ = lean_array_push(v_b_5446_, v___x_5461_);
                v___y_5448_ = v___x_5462_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6___boxed(
    mut v_as_5466_: *mut crate::leanh::LeanObject,
    mut v_i_5467_: *mut crate::leanh::LeanObject,
    mut v_stop_5468_: *mut crate::leanh::LeanObject,
    mut v_b_5469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5470_: usize = 0;
    let mut v_stop_boxed_5471_: usize = 0;
    let mut v_res_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5470_ = crate::leanh::lean_unbox_usize(v_i_5467_);
    crate::leanh::lean_dec(v_i_5467_);
    v_stop_boxed_5471_ = crate::leanh::lean_unbox_usize(v_stop_5468_);
    crate::leanh::lean_dec(v_stop_5468_);
    v_res_5472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_5466_, v_i_boxed_5470_, v_stop_boxed_5471_, v_b_5469_);
    crate::leanh::lean_dec_ref(v_as_5466_);
    return v_res_5472_;
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(
    mut v_as_5475_: *mut crate::leanh::LeanObject,
    mut v_start_5476_: *mut crate::leanh::LeanObject,
    mut v_stop_5477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: u8 = 0;
    v___x_5478_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___closed__0;
    v___x_5479_ = lean_nat_dec_lt(v_start_5476_, v_stop_5477_);
    if v___x_5479_ == 0 {
        return v___x_5478_;
    } else {
        let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5481_: u8 = 0;
        v___x_5480_ = lean_array_get_size(v_as_5475_);
        v___x_5481_ = lean_nat_dec_le(v_stop_5477_, v___x_5480_);
        if v___x_5481_ == 0 {
            let mut v___x_5482_: u8 = 0;
            v___x_5482_ = lean_nat_dec_lt(v_start_5476_, v___x_5480_);
            if v___x_5482_ == 0 {
                return v___x_5478_;
            } else {
                let mut v___x_5483_: usize = 0;
                let mut v___x_5484_: usize = 0;
                let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5483_ = lean_usize_of_nat(v_start_5476_);
                v___x_5484_ = lean_usize_of_nat(v___x_5480_);
                v___x_5485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_5475_, v___x_5483_, v___x_5484_, v___x_5478_);
                return v___x_5485_;
            }
        } else {
            let mut v___x_5486_: usize = 0;
            let mut v___x_5487_: usize = 0;
            let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5486_ = lean_usize_of_nat(v_start_5476_);
            v___x_5487_ = lean_usize_of_nat(v_stop_5477_);
            v___x_5488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_5475_, v___x_5486_, v___x_5487_, v___x_5478_);
            return v___x_5488_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___boxed(
    mut v_as_5489_: *mut crate::leanh::LeanObject,
    mut v_start_5490_: *mut crate::leanh::LeanObject,
    mut v_stop_5491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5492_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(v_as_5489_, v_start_5490_, v_stop_5491_);
    crate::leanh::lean_dec(v_stop_5491_);
    crate::leanh::lean_dec(v_start_5490_);
    crate::leanh::lean_dec_ref(v_as_5489_);
    return v_res_5492_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(
    mut v_x_5493_: *mut crate::leanh::LeanObject,
    mut v_x_5494_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: u8 = 0;
    v_fst_5495_ = crate::leanh::lean_ctor_get(v_x_5493_, 0);
    v_snd_5496_ = crate::leanh::lean_ctor_get(v_x_5493_, 1);
    v_fst_5497_ = crate::leanh::lean_ctor_get(v_x_5494_, 0);
    v_snd_5498_ = crate::leanh::lean_ctor_get(v_x_5494_, 1);
    v___x_5499_ = lean_nat_dec_eq(v_snd_5496_, v_snd_5498_);
    if v___x_5499_ == 0 {
        let mut v___x_5500_: u8 = 0;
        v___x_5500_ = lean_nat_dec_lt(v_snd_5498_, v_snd_5496_);
        return v___x_5500_;
    } else {
        let mut v___x_5501_: u8 = 0;
        v___x_5501_ = l_Lean_Name_lt(v_fst_5495_, v_fst_5497_);
        return v___x_5501_;
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0___boxed(
    mut v_x_5502_: *mut crate::leanh::LeanObject,
    mut v_x_5503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5504_: u8 = 0;
    let mut v_r_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5504_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v_x_5502_, v_x_5503_);
    crate::leanh::lean_dec_ref(v_x_5503_);
    crate::leanh::lean_dec_ref(v_x_5502_);
    v_r_5505_ = crate::leanh::lean_box((v_res_5504_) as usize);
    return v_r_5505_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(
    mut v_hi_5506_: *mut crate::leanh::LeanObject,
    mut v_pivot_5507_: *mut crate::leanh::LeanObject,
    mut v_as_5508_: *mut crate::leanh::LeanObject,
    mut v_i_5509_: *mut crate::leanh::LeanObject,
    mut v_k_5510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5512_: u8 = 0;
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: u8 = 0;
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: u8 = 0;
    let mut v___x_5530_: u8 = 0;
    let mut v___x_5531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5521_ = lean_nat_dec_lt(v_k_5510_, v_hi_5506_);
                if v___x_5521_ == 0 {
                    crate::leanh::lean_dec(v_k_5510_);
                    v___x_5522_ = lean_array_fswap(v_as_5508_, v_i_5509_, v_hi_5506_);
                    v___x_5523_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5523_, 0, v_i_5509_);
                    crate::leanh::lean_ctor_set(v___x_5523_, 1, v___x_5522_);
                    return v___x_5523_;
                } else {
                    v___x_5524_ = lean_array_fget_borrowed(v_as_5508_, v_k_5510_);
                    v_fst_5525_ = crate::leanh::lean_ctor_get(v___x_5524_, 0);
                    v_snd_5526_ = crate::leanh::lean_ctor_get(v___x_5524_, 1);
                    v_fst_5527_ = crate::leanh::lean_ctor_get(v_pivot_5507_, 0);
                    v_snd_5528_ = crate::leanh::lean_ctor_get(v_pivot_5507_, 1);
                    v___x_5529_ = lean_nat_dec_eq(v_snd_5526_, v_snd_5528_);
                    if v___x_5529_ == 0 {
                        v___x_5530_ = lean_nat_dec_lt(v_snd_5528_, v_snd_5526_);
                        v___y_5512_ = v___x_5530_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5531_ = l_Lean_Name_lt(v_fst_5525_, v_fst_5527_);
                        v___y_5512_ = v___x_5531_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5512_ == 0 {
                    v___x_5513_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5514_ = lean_nat_add(v_k_5510_, v___x_5513_);
                    crate::leanh::lean_dec(v_k_5510_);
                    v_k_5510_ = v___x_5514_;
                    state = 0;
                    continue;
                } else {
                    v___x_5516_ = lean_array_fswap(v_as_5508_, v_i_5509_, v_k_5510_);
                    v___x_5517_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5518_ = lean_nat_add(v_i_5509_, v___x_5517_);
                    crate::leanh::lean_dec(v_i_5509_);
                    v___x_5519_ = lean_nat_add(v_k_5510_, v___x_5517_);
                    crate::leanh::lean_dec(v_k_5510_);
                    v_as_5508_ = v___x_5516_;
                    v_i_5509_ = v___x_5518_;
                    v_k_5510_ = v___x_5519_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg___boxed(
    mut v_hi_5532_: *mut crate::leanh::LeanObject,
    mut v_pivot_5533_: *mut crate::leanh::LeanObject,
    mut v_as_5534_: *mut crate::leanh::LeanObject,
    mut v_i_5535_: *mut crate::leanh::LeanObject,
    mut v_k_5536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5537_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_5532_, v_pivot_5533_, v_as_5534_, v_i_5535_, v_k_5536_);
    crate::leanh::lean_dec_ref(v_pivot_5533_);
    crate::leanh::lean_dec(v_hi_5532_);
    return v_res_5537_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(
    mut v_n_5538_: *mut crate::leanh::LeanObject,
    mut v_as_5539_: *mut crate::leanh::LeanObject,
    mut v_lo_5540_: *mut crate::leanh::LeanObject,
    mut v_hi_5541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: u8 = 0;
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: u8 = 0;
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: u8 = 0;
    let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: u8 = 0;
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: u8 = 0;
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5553_ = lean_nat_dec_lt(v_lo_5540_, v_hi_5541_);
                if v___x_5553_ == 0 {
                    crate::leanh::lean_dec(v_lo_5540_);
                    return v_as_5539_;
                } else {
                    v___x_5554_ = lean_nat_add(v_lo_5540_, v_hi_5541_);
                    v___x_5555_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_5556_ = lean_nat_shiftr(v___x_5554_, v___x_5555_);
                    crate::leanh::lean_dec(v___x_5554_);
                    v___x_5569_ = lean_array_fget_borrowed(v_as_5539_, v_mid_5556_);
                    v___x_5570_ = lean_array_fget_borrowed(v_as_5539_, v_lo_5540_);
                    v___x_5571_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_5569_, v___x_5570_);
                    if v___x_5571_ == 0 {
                        v___y_5564_ = v_as_5539_;
                        state = 3;
                        continue;
                    } else {
                        v___x_5572_ = lean_array_fswap(v_as_5539_, v_lo_5540_, v_mid_5556_);
                        v___y_5564_ = v___x_5572_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_5544_ = lean_array_fget(v___y_5543_, v_hi_5541_);
                crate::leanh::lean_inc_n(v_lo_5540_, 2);
                v___x_5545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_5541_, v_pivot_5544_, v___y_5543_, v_lo_5540_, v_lo_5540_);
                crate::leanh::lean_dec(v_pivot_5544_);
                v_fst_5546_ = crate::leanh::lean_ctor_get(v___x_5545_, 0);
                crate::leanh::lean_inc(v_fst_5546_);
                v_snd_5547_ = crate::leanh::lean_ctor_get(v___x_5545_, 1);
                crate::leanh::lean_inc(v_snd_5547_);
                crate::leanh::lean_dec_ref(v___x_5545_);
                v___x_5548_ = lean_nat_dec_le(v_hi_5541_, v_fst_5546_);
                if v___x_5548_ == 0 {
                    v___x_5549_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_5538_, v_snd_5547_, v_lo_5540_, v_fst_5546_);
                    v___x_5550_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5551_ = lean_nat_add(v_fst_5546_, v___x_5550_);
                    crate::leanh::lean_dec(v_fst_5546_);
                    v_as_5539_ = v___x_5549_;
                    v_lo_5540_ = v___x_5551_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_5546_);
                    crate::leanh::lean_dec(v_lo_5540_);
                    return v_snd_5547_;
                }
            }
            2 => {
                v___x_5559_ = lean_array_fget_borrowed(v___y_5558_, v_mid_5556_);
                v___x_5560_ = lean_array_fget_borrowed(v___y_5558_, v_hi_5541_);
                v___x_5561_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_5559_, v___x_5560_);
                if v___x_5561_ == 0 {
                    crate::leanh::lean_dec(v_mid_5556_);
                    v___y_5543_ = v___y_5558_;
                    state = 1;
                    continue;
                } else {
                    v___x_5562_ = lean_array_fswap(v___y_5558_, v_mid_5556_, v_hi_5541_);
                    crate::leanh::lean_dec(v_mid_5556_);
                    v___y_5543_ = v___x_5562_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5565_ = lean_array_fget_borrowed(v___y_5564_, v_hi_5541_);
                v___x_5566_ = lean_array_fget_borrowed(v___y_5564_, v_lo_5540_);
                v___x_5567_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_5565_, v___x_5566_);
                if v___x_5567_ == 0 {
                    v___y_5558_ = v___y_5564_;
                    state = 2;
                    continue;
                } else {
                    v___x_5568_ = lean_array_fswap(v___y_5564_, v_lo_5540_, v_hi_5541_);
                    v___y_5558_ = v___x_5568_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___boxed(
    mut v_n_5573_: *mut crate::leanh::LeanObject,
    mut v_as_5574_: *mut crate::leanh::LeanObject,
    mut v_lo_5575_: *mut crate::leanh::LeanObject,
    mut v_hi_5576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_5573_, v_as_5574_, v_lo_5575_, v_hi_5576_);
    crate::leanh::lean_dec(v_hi_5576_);
    crate::leanh::lean_dec(v_n_5573_);
    return v_res_5577_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___lam__0(
    mut v_ps_5578_: *mut crate::leanh::LeanObject,
    mut v_k_5579_: *mut crate::leanh::LeanObject,
    mut v_v_5580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5581_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5581_, 0, v_k_5579_);
    crate::leanh::lean_ctor_set(v___x_5581_, 1, v_v_5580_);
    v___x_5582_ = lean_array_push(v_ps_5578_, v___x_5581_);
    return v___x_5582_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___lam__0(
    mut v_f_5583_: *mut crate::leanh::LeanObject,
    mut v_x1_5584_: *mut crate::leanh::LeanObject,
    mut v_x2_5585_: *mut crate::leanh::LeanObject,
    mut v_x3_5586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5587_ = crate::leanh::lean_apply_3(v_f_5583_, v_x1_5584_, v_x2_5585_, v_x3_5586_);
    return v___x_5587_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(
    mut v_f_5588_: *mut crate::leanh::LeanObject,
    mut v_keys_5589_: *mut crate::leanh::LeanObject,
    mut v_vals_5590_: *mut crate::leanh::LeanObject,
    mut v_i_5591_: *mut crate::leanh::LeanObject,
    mut v_acc_5592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: u8 = 0;
    let mut v_k_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5593_ = lean_array_get_size(v_keys_5589_);
                v___x_5594_ = lean_nat_dec_lt(v_i_5591_, v___x_5593_);
                if v___x_5594_ == 0 {
                    crate::leanh::lean_dec(v_i_5591_);
                    crate::leanh::lean_dec(v_f_5588_);
                    return v_acc_5592_;
                } else {
                    v_k_5595_ = lean_array_fget_borrowed(v_keys_5589_, v_i_5591_);
                    v_v_5596_ = lean_array_fget_borrowed(v_vals_5590_, v_i_5591_);
                    crate::leanh::lean_inc(v_f_5588_);
                    crate::leanh::lean_inc(v_v_5596_);
                    crate::leanh::lean_inc(v_k_5595_);
                    v___x_5597_ =
                        crate::leanh::lean_apply_3(v_f_5588_, v_acc_5592_, v_k_5595_, v_v_5596_);
                    v___x_5598_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5599_ = lean_nat_add(v_i_5591_, v___x_5598_);
                    crate::leanh::lean_dec(v_i_5591_);
                    v_i_5591_ = v___x_5599_;
                    v_acc_5592_ = v___x_5597_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg___boxed(
    mut v_f_5601_: *mut crate::leanh::LeanObject,
    mut v_keys_5602_: *mut crate::leanh::LeanObject,
    mut v_vals_5603_: *mut crate::leanh::LeanObject,
    mut v_i_5604_: *mut crate::leanh::LeanObject,
    mut v_acc_5605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_5601_, v_keys_5602_, v_vals_5603_, v_i_5604_, v_acc_5605_);
    crate::leanh::lean_dec_ref(v_vals_5603_);
    crate::leanh::lean_dec_ref(v_keys_5602_);
    return v_res_5606_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(
    mut v_f_5607_: *mut crate::leanh::LeanObject,
    mut v_x_5608_: *mut crate::leanh::LeanObject,
    mut v_x_5609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5608_) == 0 {
        let mut v_es_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5613_: u8 = 0;
        v_es_5610_ = crate::leanh::lean_ctor_get(v_x_5608_, 0);
        v___x_5611_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5612_ = lean_array_get_size(v_es_5610_);
        v___x_5613_ = lean_nat_dec_lt(v___x_5611_, v___x_5612_);
        if v___x_5613_ == 0 {
            crate::leanh::lean_dec(v_f_5607_);
            return v_x_5609_;
        } else {
            let mut v___x_5614_: u8 = 0;
            v___x_5614_ = lean_nat_dec_le(v___x_5612_, v___x_5612_);
            if v___x_5614_ == 0 {
                if v___x_5613_ == 0 {
                    crate::leanh::lean_dec(v_f_5607_);
                    return v_x_5609_;
                } else {
                    let mut v___x_5615_: usize = 0;
                    let mut v___x_5616_: usize = 0;
                    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5615_ = 0usize;
                    v___x_5616_ = lean_usize_of_nat(v___x_5612_);
                    v___x_5617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_5607_, v_es_5610_, v___x_5615_, v___x_5616_, v_x_5609_);
                    return v___x_5617_;
                }
            } else {
                let mut v___x_5618_: usize = 0;
                let mut v___x_5619_: usize = 0;
                let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5618_ = 0usize;
                v___x_5619_ = lean_usize_of_nat(v___x_5612_);
                v___x_5620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_5607_, v_es_5610_, v___x_5618_, v___x_5619_, v_x_5609_);
                return v___x_5620_;
            }
        }
    } else {
        let mut v_ks_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_5621_ = crate::leanh::lean_ctor_get(v_x_5608_, 0);
        v_vs_5622_ = crate::leanh::lean_ctor_get(v_x_5608_, 1);
        v___x_5623_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5624_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_5607_, v_ks_5621_, v_vs_5622_, v___x_5623_, v_x_5609_);
        return v___x_5624_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(
    mut v_f_5625_: *mut crate::leanh::LeanObject,
    mut v_as_5626_: *mut crate::leanh::LeanObject,
    mut v_i_5627_: usize,
    mut v_stop_5628_: usize,
    mut v_b_5629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: usize = 0;
    let mut v___x_5633_: usize = 0;
    let mut v___x_5635_: u8 = 0;
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5635_ = lean_usize_dec_eq(v_i_5627_, v_stop_5628_);
                if v___x_5635_ == 0 {
                    v___x_5636_ = lean_array_uget_borrowed(v_as_5626_, v_i_5627_);
                    match crate::leanh::lean_obj_tag(v___x_5636_) {
                        0 => {
                            v_key_5637_ = crate::leanh::lean_ctor_get(v___x_5636_, 0);
                            v_val_5638_ = crate::leanh::lean_ctor_get(v___x_5636_, 1);
                            crate::leanh::lean_inc(v_f_5625_);
                            crate::leanh::lean_inc(v_val_5638_);
                            crate::leanh::lean_inc(v_key_5637_);
                            v___x_5639_ = crate::leanh::lean_apply_3(
                                v_f_5625_,
                                v_b_5629_,
                                v_key_5637_,
                                v_val_5638_,
                            );
                            v___y_5631_ = v___x_5639_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_5640_ = crate::leanh::lean_ctor_get(v___x_5636_, 0);
                            crate::leanh::lean_inc(v_f_5625_);
                            v___x_5641_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_5625_, v_node_5640_, v_b_5629_);
                            v___y_5631_ = v___x_5641_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_5631_ = v_b_5629_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_f_5625_);
                    return v_b_5629_;
                }
            }
            1 => {
                v___x_5632_ = 1usize;
                v___x_5633_ = lean_usize_add(v_i_5627_, v___x_5632_);
                v_i_5627_ = v___x_5633_;
                v_b_5629_ = v___y_5631_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg___boxed(
    mut v_f_5642_: *mut crate::leanh::LeanObject,
    mut v_as_5643_: *mut crate::leanh::LeanObject,
    mut v_i_5644_: *mut crate::leanh::LeanObject,
    mut v_stop_5645_: *mut crate::leanh::LeanObject,
    mut v_b_5646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5647_: usize = 0;
    let mut v_stop_boxed_5648_: usize = 0;
    let mut v_res_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5647_ = crate::leanh::lean_unbox_usize(v_i_5644_);
    crate::leanh::lean_dec(v_i_5644_);
    v_stop_boxed_5648_ = crate::leanh::lean_unbox_usize(v_stop_5645_);
    crate::leanh::lean_dec(v_stop_5645_);
    v_res_5649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_5642_, v_as_5643_, v_i_boxed_5647_, v_stop_boxed_5648_, v_b_5646_);
    crate::leanh::lean_dec_ref(v_as_5643_);
    return v_res_5649_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg___boxed(
    mut v_f_5650_: *mut crate::leanh::LeanObject,
    mut v_x_5651_: *mut crate::leanh::LeanObject,
    mut v_x_5652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5653_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_5650_, v_x_5651_, v_x_5652_);
    crate::leanh::lean_dec_ref(v_x_5651_);
    return v_res_5653_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(
    mut v_map_5654_: *mut crate::leanh::LeanObject,
    mut v_f_5655_: *mut crate::leanh::LeanObject,
    mut v_init_5656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5657_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_5657_, 0, v_f_5655_);
    v___x_5658_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v___f_5657_, v_map_5654_, v_init_5656_);
    return v___x_5658_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___boxed(
    mut v_map_5659_: *mut crate::leanh::LeanObject,
    mut v_f_5660_: *mut crate::leanh::LeanObject,
    mut v_init_5661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5662_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_map_5659_, v_f_5660_, v_init_5661_);
    crate::leanh::lean_dec_ref(v_map_5659_);
    return v_res_5662_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(
    mut v_m_5666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5667_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__0;
    v___x_5668_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__1;
    v___x_5669_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_m_5666_, v___f_5667_, v___x_5668_);
    return v___x_5669_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___boxed(
    mut v_m_5670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5671_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_m_5670_);
    crate::leanh::lean_dec_ref(v_m_5670_);
    return v_res_5671_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5673_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__0;
    v___x_5674_ = l_Lean_stringToMessageData(v___x_5673_);
    return v___x_5674_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5676_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__2;
    v___x_5677_ = l_Lean_stringToMessageData(v___x_5676_);
    return v___x_5677_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5679_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__4;
    v___x_5680_ = l_Lean_stringToMessageData(v___x_5679_);
    return v___x_5680_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5682_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__6;
    v___x_5683_ = l_Lean_stringToMessageData(v___x_5682_);
    return v___x_5683_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5685_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__8;
    v___x_5686_ = l_Lean_stringToMessageData(v___x_5685_);
    return v___x_5686_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5688_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10;
    v___x_5689_ = l_Lean_stringToMessageData(v___x_5688_);
    return v___x_5689_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5691_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12;
    v___x_5692_ = l_Lean_stringToMessageData(v___x_5691_);
    return v___x_5692_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(
    mut v_msg_5693_: *mut crate::leanh::LeanObject,
    mut v_declHint_5694_: *mut crate::leanh::LeanObject,
    mut v___y_5695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: u8 = 0;
    let mut v_isExporting_5700_: u8 = 0;
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: u8 = 0;
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5722_: u8 = 0;
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: u8 = 0;
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5754_: u8 = 0;
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5697_ = lean_st_ref_get(v___y_5695_);
                v_env_5698_ = crate::leanh::lean_ctor_get(v___x_5697_, 0);
                crate::leanh::lean_inc_ref(v_env_5698_);
                crate::leanh::lean_dec(v___x_5697_);
                v___x_5699_ = l_Lean_Name_isAnonymous(v_declHint_5694_);
                if v___x_5699_ == 0 {
                    v_isExporting_5700_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_5698_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5700_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_5698_);
                        crate::leanh::lean_dec(v_declHint_5694_);
                        v___x_5701_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5701_, 0, v_msg_5693_);
                        return v___x_5701_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_5698_);
                        v___x_5702_ = l_Lean_Environment_setExporting(v_env_5698_, v___x_5699_);
                        crate::leanh::lean_inc(v_declHint_5694_);
                        crate::leanh::lean_inc_ref(v___x_5702_);
                        v___x_5703_ = l_Lean_Environment_contains(
                            v___x_5702_,
                            v_declHint_5694_,
                            v_isExporting_5700_,
                        );
                        if v___x_5703_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5702_);
                            crate::leanh::lean_dec_ref(v_env_5698_);
                            crate::leanh::lean_dec(v_declHint_5694_);
                            v___x_5704_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5704_, 0, v_msg_5693_);
                            return v___x_5704_;
                        } else {
                            v___x_5705_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2);
                            v___x_5706_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5);
                            v___x_5707_ = l_Lean_Options_empty;
                            v___x_5708_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5708_, 0, v___x_5702_);
                            crate::leanh::lean_ctor_set(v___x_5708_, 1, v___x_5705_);
                            crate::leanh::lean_ctor_set(v___x_5708_, 2, v___x_5706_);
                            crate::leanh::lean_ctor_set(v___x_5708_, 3, v___x_5707_);
                            crate::leanh::lean_inc(v_declHint_5694_);
                            v___x_5709_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5694_, v___x_5699_);
                            v_c_5710_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_5710_, 0, v___x_5708_);
                            crate::leanh::lean_ctor_set(v_c_5710_, 1, v___x_5709_);
                            v___x_5711_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5698_,
                                v_declHint_5694_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5711_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_5698_);
                                crate::leanh::lean_dec(v_declHint_5694_);
                                v___x_5712_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1);
                                v___x_5713_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5713_, 0, v___x_5712_);
                                crate::leanh::lean_ctor_set(v___x_5713_, 1, v_c_5710_);
                                v___x_5714_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3);
                                v___x_5715_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5715_, 0, v___x_5713_);
                                crate::leanh::lean_ctor_set(v___x_5715_, 1, v___x_5714_);
                                v___x_5716_ = l_Lean_MessageData_note(v___x_5715_);
                                v___x_5717_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5717_, 0, v_msg_5693_);
                                crate::leanh::lean_ctor_set(v___x_5717_, 1, v___x_5716_);
                                v___x_5718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5718_, 0, v___x_5717_);
                                return v___x_5718_;
                            } else {
                                v_val_5719_ = crate::leanh::lean_ctor_get(v___x_5711_, 0);
                                v_isSharedCheck_5754_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5711_)) as u8;
                                if v_isSharedCheck_5754_ == 0 {
                                    v___x_5721_ = v___x_5711_;
                                    v_isShared_5722_ = v_isSharedCheck_5754_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_5719_);
                                    crate::leanh::lean_dec(v___x_5711_);
                                    v___x_5721_ = crate::leanh::lean_box(0);
                                    v_isShared_5722_ = v_isSharedCheck_5754_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_5698_);
                    crate::leanh::lean_dec(v_declHint_5694_);
                    v___x_5755_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5755_, 0, v_msg_5693_);
                    return v___x_5755_;
                }
            }
            1 => {
                v___x_5723_ = crate::leanh::lean_box(0);
                v___x_5724_ = l_Lean_Environment_header(v_env_5698_);
                crate::leanh::lean_dec_ref(v_env_5698_);
                v___x_5725_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5724_);
                v_mod_5726_ = lean_array_get(v___x_5723_, v___x_5725_, v_val_5719_);
                crate::leanh::lean_dec(v_val_5719_);
                crate::leanh::lean_dec_ref(v___x_5725_);
                v___x_5727_ = l_Lean_isPrivateName(v_declHint_5694_);
                crate::leanh::lean_dec(v_declHint_5694_);
                if v___x_5727_ == 0 {
                    v___x_5728_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5);
                    v___x_5729_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5729_, 0, v___x_5728_);
                    crate::leanh::lean_ctor_set(v___x_5729_, 1, v_c_5710_);
                    v___x_5730_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7);
                    v___x_5731_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5731_, 0, v___x_5729_);
                    crate::leanh::lean_ctor_set(v___x_5731_, 1, v___x_5730_);
                    v___x_5732_ = l_Lean_MessageData_ofName(v_mod_5726_);
                    v___x_5733_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5733_, 0, v___x_5731_);
                    crate::leanh::lean_ctor_set(v___x_5733_, 1, v___x_5732_);
                    v___x_5734_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9);
                    v___x_5735_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5735_, 0, v___x_5733_);
                    crate::leanh::lean_ctor_set(v___x_5735_, 1, v___x_5734_);
                    v___x_5736_ = l_Lean_MessageData_note(v___x_5735_);
                    v___x_5737_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5737_, 0, v_msg_5693_);
                    crate::leanh::lean_ctor_set(v___x_5737_, 1, v___x_5736_);
                    if v_isShared_5722_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5721_, 0);
                        crate::leanh::lean_ctor_set(v___x_5721_, 0, v___x_5737_);
                        v___x_5739_ = v___x_5721_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5740_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5740_, 0, v___x_5737_);
                        v___x_5739_ = v_reuseFailAlloc_5740_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5741_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1);
                    v___x_5742_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5742_, 0, v___x_5741_);
                    crate::leanh::lean_ctor_set(v___x_5742_, 1, v_c_5710_);
                    v___x_5743_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11);
                    v___x_5744_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5744_, 0, v___x_5742_);
                    crate::leanh::lean_ctor_set(v___x_5744_, 1, v___x_5743_);
                    v___x_5745_ = l_Lean_MessageData_ofName(v_mod_5726_);
                    v___x_5746_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5746_, 0, v___x_5744_);
                    crate::leanh::lean_ctor_set(v___x_5746_, 1, v___x_5745_);
                    v___x_5747_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13);
                    v___x_5748_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5748_, 0, v___x_5746_);
                    crate::leanh::lean_ctor_set(v___x_5748_, 1, v___x_5747_);
                    v___x_5749_ = l_Lean_MessageData_note(v___x_5748_);
                    v___x_5750_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5750_, 0, v_msg_5693_);
                    crate::leanh::lean_ctor_set(v___x_5750_, 1, v___x_5749_);
                    if v_isShared_5722_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5721_, 0);
                        crate::leanh::lean_ctor_set(v___x_5721_, 0, v___x_5750_);
                        v___x_5752_ = v___x_5721_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5753_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5753_, 0, v___x_5750_);
                        v___x_5752_ = v_reuseFailAlloc_5753_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5739_;
            }
            3 => {
                return v___x_5752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___boxed(
    mut v_msg_5756_: *mut crate::leanh::LeanObject,
    mut v_declHint_5757_: *mut crate::leanh::LeanObject,
    mut v___y_5758_: *mut crate::leanh::LeanObject,
    mut v___y_5759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5760_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_5756_, v_declHint_5757_, v___y_5758_);
    crate::leanh::lean_dec(v___y_5758_);
    return v_res_5760_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(
    mut v_msg_5761_: *mut crate::leanh::LeanObject,
    mut v_declHint_5762_: *mut crate::leanh::LeanObject,
    mut v___y_5763_: *mut crate::leanh::LeanObject,
    mut v___y_5764_: *mut crate::leanh::LeanObject,
    mut v___y_5765_: *mut crate::leanh::LeanObject,
    mut v___y_5766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5772_: u8 = 0;
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5768_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_5761_, v_declHint_5762_, v___y_5766_);
                v_a_5769_ = crate::leanh::lean_ctor_get(v___x_5768_, 0);
                v_isSharedCheck_5778_ = (!crate::leanh::lean_is_exclusive(v___x_5768_)) as u8;
                if v_isSharedCheck_5778_ == 0 {
                    v___x_5771_ = v___x_5768_;
                    v_isShared_5772_ = v_isSharedCheck_5778_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5769_);
                    crate::leanh::lean_dec(v___x_5768_);
                    v___x_5771_ = crate::leanh::lean_box(0);
                    v_isShared_5772_ = v_isSharedCheck_5778_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5773_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5774_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5774_, 0, v___x_5773_);
                crate::leanh::lean_ctor_set(v___x_5774_, 1, v_a_5769_);
                if v_isShared_5772_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5771_, 0, v___x_5774_);
                    v___x_5776_ = v___x_5771_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5777_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5777_, 0, v___x_5774_);
                    v___x_5776_ = v_reuseFailAlloc_5777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5776_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16___boxed(
    mut v_msg_5779_: *mut crate::leanh::LeanObject,
    mut v_declHint_5780_: *mut crate::leanh::LeanObject,
    mut v___y_5781_: *mut crate::leanh::LeanObject,
    mut v___y_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
    mut v___y_5784_: *mut crate::leanh::LeanObject,
    mut v___y_5785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5786_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(v_msg_5779_, v_declHint_5780_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
    crate::leanh::lean_dec(v___y_5784_);
    crate::leanh::lean_dec_ref(v___y_5783_);
    crate::leanh::lean_dec(v___y_5782_);
    crate::leanh::lean_dec_ref(v___y_5781_);
    return v_res_5786_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(
    mut v_msg_5787_: *mut crate::leanh::LeanObject,
    mut v___y_5788_: *mut crate::leanh::LeanObject,
    mut v___y_5789_: *mut crate::leanh::LeanObject,
    mut v___y_5790_: *mut crate::leanh::LeanObject,
    mut v___y_5791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5798_: u8 = 0;
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5793_ = crate::leanh::lean_ctor_get(v___y_5790_, 5);
                v___x_5794_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v_msg_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_);
                v_a_5795_ = crate::leanh::lean_ctor_get(v___x_5794_, 0);
                v_isSharedCheck_5803_ = (!crate::leanh::lean_is_exclusive(v___x_5794_)) as u8;
                if v_isSharedCheck_5803_ == 0 {
                    v___x_5797_ = v___x_5794_;
                    v_isShared_5798_ = v_isSharedCheck_5803_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5795_);
                    crate::leanh::lean_dec(v___x_5794_);
                    v___x_5797_ = crate::leanh::lean_box(0);
                    v_isShared_5798_ = v_isSharedCheck_5803_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_5793_);
                v___x_5799_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5799_, 0, v_ref_5793_);
                crate::leanh::lean_ctor_set(v___x_5799_, 1, v_a_5795_);
                if v_isShared_5798_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5797_, 1);
                    crate::leanh::lean_ctor_set(v___x_5797_, 0, v___x_5799_);
                    v___x_5801_ = v___x_5797_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5802_, 0, v___x_5799_);
                    v___x_5801_ = v_reuseFailAlloc_5802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg___boxed(
    mut v_msg_5804_: *mut crate::leanh::LeanObject,
    mut v___y_5805_: *mut crate::leanh::LeanObject,
    mut v___y_5806_: *mut crate::leanh::LeanObject,
    mut v___y_5807_: *mut crate::leanh::LeanObject,
    mut v___y_5808_: *mut crate::leanh::LeanObject,
    mut v___y_5809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5810_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_);
    crate::leanh::lean_dec(v___y_5808_);
    crate::leanh::lean_dec_ref(v___y_5807_);
    crate::leanh::lean_dec(v___y_5806_);
    crate::leanh::lean_dec_ref(v___y_5805_);
    return v_res_5810_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(
    mut v_ref_5811_: *mut crate::leanh::LeanObject,
    mut v_msg_5812_: *mut crate::leanh::LeanObject,
    mut v___y_5813_: *mut crate::leanh::LeanObject,
    mut v___y_5814_: *mut crate::leanh::LeanObject,
    mut v___y_5815_: *mut crate::leanh::LeanObject,
    mut v___y_5816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5830_: u8 = 0;
    let mut v_cancelTk_x3f_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5832_: u8 = 0;
    let mut v_inheritedTraceOptions_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5818_ = crate::leanh::lean_ctor_get(v___y_5815_, 0);
    v_fileMap_5819_ = crate::leanh::lean_ctor_get(v___y_5815_, 1);
    v_options_5820_ = crate::leanh::lean_ctor_get(v___y_5815_, 2);
    v_currRecDepth_5821_ = crate::leanh::lean_ctor_get(v___y_5815_, 3);
    v_maxRecDepth_5822_ = crate::leanh::lean_ctor_get(v___y_5815_, 4);
    v_ref_5823_ = crate::leanh::lean_ctor_get(v___y_5815_, 5);
    v_currNamespace_5824_ = crate::leanh::lean_ctor_get(v___y_5815_, 6);
    v_openDecls_5825_ = crate::leanh::lean_ctor_get(v___y_5815_, 7);
    v_initHeartbeats_5826_ = crate::leanh::lean_ctor_get(v___y_5815_, 8);
    v_maxHeartbeats_5827_ = crate::leanh::lean_ctor_get(v___y_5815_, 9);
    v_quotContext_5828_ = crate::leanh::lean_ctor_get(v___y_5815_, 10);
    v_currMacroScope_5829_ = crate::leanh::lean_ctor_get(v___y_5815_, 11);
    v_diag_5830_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5815_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5831_ = crate::leanh::lean_ctor_get(v___y_5815_, 12);
    v_suppressElabErrors_5832_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5815_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5833_ = crate::leanh::lean_ctor_get(v___y_5815_, 13);
    v_ref_5834_ = l_Lean_replaceRef(v_ref_5811_, v_ref_5823_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5833_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5831_);
    crate::leanh::lean_inc(v_currMacroScope_5829_);
    crate::leanh::lean_inc(v_quotContext_5828_);
    crate::leanh::lean_inc(v_maxHeartbeats_5827_);
    crate::leanh::lean_inc(v_initHeartbeats_5826_);
    crate::leanh::lean_inc(v_openDecls_5825_);
    crate::leanh::lean_inc(v_currNamespace_5824_);
    crate::leanh::lean_inc(v_maxRecDepth_5822_);
    crate::leanh::lean_inc(v_currRecDepth_5821_);
    crate::leanh::lean_inc_ref(v_options_5820_);
    crate::leanh::lean_inc_ref(v_fileMap_5819_);
    crate::leanh::lean_inc_ref(v_fileName_5818_);
    v___x_5835_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5835_, 0, v_fileName_5818_);
    crate::leanh::lean_ctor_set(v___x_5835_, 1, v_fileMap_5819_);
    crate::leanh::lean_ctor_set(v___x_5835_, 2, v_options_5820_);
    crate::leanh::lean_ctor_set(v___x_5835_, 3, v_currRecDepth_5821_);
    crate::leanh::lean_ctor_set(v___x_5835_, 4, v_maxRecDepth_5822_);
    crate::leanh::lean_ctor_set(v___x_5835_, 5, v_ref_5834_);
    crate::leanh::lean_ctor_set(v___x_5835_, 6, v_currNamespace_5824_);
    crate::leanh::lean_ctor_set(v___x_5835_, 7, v_openDecls_5825_);
    crate::leanh::lean_ctor_set(v___x_5835_, 8, v_initHeartbeats_5826_);
    crate::leanh::lean_ctor_set(v___x_5835_, 9, v_maxHeartbeats_5827_);
    crate::leanh::lean_ctor_set(v___x_5835_, 10, v_quotContext_5828_);
    crate::leanh::lean_ctor_set(v___x_5835_, 11, v_currMacroScope_5829_);
    crate::leanh::lean_ctor_set(v___x_5835_, 12, v_cancelTk_x3f_5831_);
    crate::leanh::lean_ctor_set(v___x_5835_, 13, v_inheritedTraceOptions_5833_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5835_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5830_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5835_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5832_,
    );
    v___x_5836_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_5812_, v___y_5813_, v___y_5814_, v___x_5835_, v___y_5816_);
    crate::leanh::lean_dec_ref_known(v___x_5835_, 14);
    return v___x_5836_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg___boxed(
    mut v_ref_5837_: *mut crate::leanh::LeanObject,
    mut v_msg_5838_: *mut crate::leanh::LeanObject,
    mut v___y_5839_: *mut crate::leanh::LeanObject,
    mut v___y_5840_: *mut crate::leanh::LeanObject,
    mut v___y_5841_: *mut crate::leanh::LeanObject,
    mut v___y_5842_: *mut crate::leanh::LeanObject,
    mut v___y_5843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5844_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_5837_, v_msg_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_);
    crate::leanh::lean_dec(v___y_5842_);
    crate::leanh::lean_dec_ref(v___y_5841_);
    crate::leanh::lean_dec(v___y_5840_);
    crate::leanh::lean_dec_ref(v___y_5839_);
    crate::leanh::lean_dec(v_ref_5837_);
    return v_res_5844_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(
    mut v_ref_5845_: *mut crate::leanh::LeanObject,
    mut v_msg_5846_: *mut crate::leanh::LeanObject,
    mut v_declHint_5847_: *mut crate::leanh::LeanObject,
    mut v___y_5848_: *mut crate::leanh::LeanObject,
    mut v___y_5849_: *mut crate::leanh::LeanObject,
    mut v___y_5850_: *mut crate::leanh::LeanObject,
    mut v___y_5851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5853_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(v_msg_5846_, v_declHint_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_);
    v_a_5854_ = crate::leanh::lean_ctor_get(v___x_5853_, 0);
    crate::leanh::lean_inc(v_a_5854_);
    crate::leanh::lean_dec_ref(v___x_5853_);
    v___x_5855_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_5845_, v_a_5854_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_);
    return v___x_5855_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg___boxed(
    mut v_ref_5856_: *mut crate::leanh::LeanObject,
    mut v_msg_5857_: *mut crate::leanh::LeanObject,
    mut v_declHint_5858_: *mut crate::leanh::LeanObject,
    mut v___y_5859_: *mut crate::leanh::LeanObject,
    mut v___y_5860_: *mut crate::leanh::LeanObject,
    mut v___y_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
    mut v___y_5863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5864_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_5856_, v_msg_5857_, v_declHint_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___y_5862_);
    crate::leanh::lean_dec(v___y_5862_);
    crate::leanh::lean_dec_ref(v___y_5861_);
    crate::leanh::lean_dec(v___y_5860_);
    crate::leanh::lean_dec_ref(v___y_5859_);
    crate::leanh::lean_dec(v_ref_5856_);
    return v_res_5864_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5866_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__0;
    v___x_5867_ = l_Lean_stringToMessageData(v___x_5866_);
    return v___x_5867_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(
    mut v_ref_5868_: *mut crate::leanh::LeanObject,
    mut v_constName_5869_: *mut crate::leanh::LeanObject,
    mut v___y_5870_: *mut crate::leanh::LeanObject,
    mut v___y_5871_: *mut crate::leanh::LeanObject,
    mut v___y_5872_: *mut crate::leanh::LeanObject,
    mut v___y_5873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: u8 = 0;
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5875_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1);
    v___x_5876_ = 0;
    crate::leanh::lean_inc(v_constName_5869_);
    v___x_5877_ = l_Lean_MessageData_ofConstName(v_constName_5869_, v___x_5876_);
    v___x_5878_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5878_, 0, v___x_5875_);
    crate::leanh::lean_ctor_set(v___x_5878_, 1, v___x_5877_);
    v___x_5879_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
    v___x_5880_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5880_, 0, v___x_5878_);
    crate::leanh::lean_ctor_set(v___x_5880_, 1, v___x_5879_);
    v___x_5881_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_5868_, v___x_5880_, v_constName_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_);
    return v___x_5881_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___boxed(
    mut v_ref_5882_: *mut crate::leanh::LeanObject,
    mut v_constName_5883_: *mut crate::leanh::LeanObject,
    mut v___y_5884_: *mut crate::leanh::LeanObject,
    mut v___y_5885_: *mut crate::leanh::LeanObject,
    mut v___y_5886_: *mut crate::leanh::LeanObject,
    mut v___y_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5889_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_5882_, v_constName_5883_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_);
    crate::leanh::lean_dec(v___y_5887_);
    crate::leanh::lean_dec_ref(v___y_5886_);
    crate::leanh::lean_dec(v___y_5885_);
    crate::leanh::lean_dec_ref(v___y_5884_);
    crate::leanh::lean_dec(v_ref_5882_);
    return v_res_5889_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(
    mut v_constName_5890_: *mut crate::leanh::LeanObject,
    mut v___y_5891_: *mut crate::leanh::LeanObject,
    mut v___y_5892_: *mut crate::leanh::LeanObject,
    mut v___y_5893_: *mut crate::leanh::LeanObject,
    mut v___y_5894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_5896_ = crate::leanh::lean_ctor_get(v___y_5893_, 5);
    v___x_5897_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_5896_, v_constName_5890_, v___y_5891_, v___y_5892_, v___y_5893_, v___y_5894_);
    return v___x_5897_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_constName_5898_: *mut crate::leanh::LeanObject,
    mut v___y_5899_: *mut crate::leanh::LeanObject,
    mut v___y_5900_: *mut crate::leanh::LeanObject,
    mut v___y_5901_: *mut crate::leanh::LeanObject,
    mut v___y_5902_: *mut crate::leanh::LeanObject,
    mut v___y_5903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5904_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_5898_, v___y_5899_, v___y_5900_, v___y_5901_, v___y_5902_);
    crate::leanh::lean_dec(v___y_5902_);
    crate::leanh::lean_dec_ref(v___y_5901_);
    crate::leanh::lean_dec(v___y_5900_);
    crate::leanh::lean_dec_ref(v___y_5899_);
    return v_res_5904_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(
    mut v_constName_5905_: *mut crate::leanh::LeanObject,
    mut v___y_5906_: *mut crate::leanh::LeanObject,
    mut v___y_5907_: *mut crate::leanh::LeanObject,
    mut v___y_5908_: *mut crate::leanh::LeanObject,
    mut v___y_5909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: u8 = 0;
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5919_: u8 = 0;
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5923_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5911_ = lean_st_ref_get(v___y_5909_);
                v_env_5912_ = crate::leanh::lean_ctor_get(v___x_5911_, 0);
                crate::leanh::lean_inc_ref(v_env_5912_);
                crate::leanh::lean_dec(v___x_5911_);
                v___x_5913_ = 0;
                crate::leanh::lean_inc(v_constName_5905_);
                v___x_5914_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_5912_,
                    v_constName_5905_,
                    v___x_5913_,
                );
                if crate::leanh::lean_obj_tag(v___x_5914_) == 0 {
                    v___x_5915_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_5905_, v___y_5906_, v___y_5907_, v___y_5908_, v___y_5909_);
                    return v___x_5915_;
                } else {
                    crate::leanh::lean_dec(v_constName_5905_);
                    v_val_5916_ = crate::leanh::lean_ctor_get(v___x_5914_, 0);
                    v_isSharedCheck_5923_ = (!crate::leanh::lean_is_exclusive(v___x_5914_)) as u8;
                    if v_isSharedCheck_5923_ == 0 {
                        v___x_5918_ = v___x_5914_;
                        v_isShared_5919_ = v_isSharedCheck_5923_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5916_);
                        crate::leanh::lean_dec(v___x_5914_);
                        v___x_5918_ = crate::leanh::lean_box(0);
                        v_isShared_5919_ = v_isSharedCheck_5923_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5919_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5918_, 0);
                    v___x_5921_ = v___x_5918_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5922_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5922_, 0, v_val_5916_);
                    v___x_5921_ = v_reuseFailAlloc_5922_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5921_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2___boxed(
    mut v_constName_5924_: *mut crate::leanh::LeanObject,
    mut v___y_5925_: *mut crate::leanh::LeanObject,
    mut v___y_5926_: *mut crate::leanh::LeanObject,
    mut v___y_5927_: *mut crate::leanh::LeanObject,
    mut v___y_5928_: *mut crate::leanh::LeanObject,
    mut v___y_5929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5930_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(v_constName_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_);
    crate::leanh::lean_dec(v___y_5928_);
    crate::leanh::lean_dec_ref(v___y_5927_);
    crate::leanh::lean_dec(v___y_5926_);
    crate::leanh::lean_dec_ref(v___y_5925_);
    return v_res_5930_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__3(
    mut v_a_5931_: *mut crate::leanh::LeanObject,
    mut v_a_5932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5938_: u8 = 0;
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5944_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5931_) == 0 {
                    v___x_5933_ = l_List_reverse___redArg(v_a_5932_);
                    return v___x_5933_;
                } else {
                    v_head_5934_ = crate::leanh::lean_ctor_get(v_a_5931_, 0);
                    v_tail_5935_ = crate::leanh::lean_ctor_get(v_a_5931_, 1);
                    v_isSharedCheck_5944_ = (!crate::leanh::lean_is_exclusive(v_a_5931_)) as u8;
                    if v_isSharedCheck_5944_ == 0 {
                        v___x_5937_ = v_a_5931_;
                        v_isShared_5938_ = v_isSharedCheck_5944_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5935_);
                        crate::leanh::lean_inc(v_head_5934_);
                        crate::leanh::lean_dec(v_a_5931_);
                        v___x_5937_ = crate::leanh::lean_box(0);
                        v_isShared_5938_ = v_isSharedCheck_5944_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5939_ = l_Lean_mkLevelParam(v_head_5934_);
                if v_isShared_5938_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5937_, 1, v_a_5932_);
                    crate::leanh::lean_ctor_set(v___x_5937_, 0, v___x_5939_);
                    v___x_5941_ = v___x_5937_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5943_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5943_, 0, v___x_5939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5943_, 1, v_a_5932_);
                    v___x_5941_ = v_reuseFailAlloc_5943_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5931_ = v_tail_5935_;
                v_a_5932_ = v___x_5941_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(
    mut v_constName_5945_: *mut crate::leanh::LeanObject,
    mut v___y_5946_: *mut crate::leanh::LeanObject,
    mut v___y_5947_: *mut crate::leanh::LeanObject,
    mut v___y_5948_: *mut crate::leanh::LeanObject,
    mut v___y_5949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5955_: u8 = 0;
    let mut v_levelParams_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5963_: u8 = 0;
    let mut v_a_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5967_: u8 = 0;
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_constName_5945_);
                v___x_5951_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(v_constName_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_);
                if crate::leanh::lean_obj_tag(v___x_5951_) == 0 {
                    v_a_5952_ = crate::leanh::lean_ctor_get(v___x_5951_, 0);
                    v_isSharedCheck_5963_ = (!crate::leanh::lean_is_exclusive(v___x_5951_)) as u8;
                    if v_isSharedCheck_5963_ == 0 {
                        v___x_5954_ = v___x_5951_;
                        v_isShared_5955_ = v_isSharedCheck_5963_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5952_);
                        crate::leanh::lean_dec(v___x_5951_);
                        v___x_5954_ = crate::leanh::lean_box(0);
                        v_isShared_5955_ = v_isSharedCheck_5963_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_constName_5945_);
                    v_a_5964_ = crate::leanh::lean_ctor_get(v___x_5951_, 0);
                    v_isSharedCheck_5971_ = (!crate::leanh::lean_is_exclusive(v___x_5951_)) as u8;
                    if v_isSharedCheck_5971_ == 0 {
                        v___x_5966_ = v___x_5951_;
                        v_isShared_5967_ = v_isSharedCheck_5971_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5964_);
                        crate::leanh::lean_dec(v___x_5951_);
                        v___x_5966_ = crate::leanh::lean_box(0);
                        v_isShared_5967_ = v_isSharedCheck_5971_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_5956_ = crate::leanh::lean_ctor_get(v_a_5952_, 1);
                crate::leanh::lean_inc(v_levelParams_5956_);
                crate::leanh::lean_dec(v_a_5952_);
                v___x_5957_ = crate::leanh::lean_box(0);
                v___x_5958_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__3(v_levelParams_5956_, v___x_5957_);
                v___x_5959_ = l_Lean_mkConst(v_constName_5945_, v___x_5958_);
                if v_isShared_5955_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5954_, 0, v___x_5959_);
                    v___x_5961_ = v___x_5954_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5962_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5962_, 0, v___x_5959_);
                    v___x_5961_ = v_reuseFailAlloc_5962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5961_;
            }
            3 => {
                if v_isShared_5967_ == 0 {
                    v___x_5969_ = v___x_5966_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5970_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5970_, 0, v_a_5964_);
                    v___x_5969_ = v_reuseFailAlloc_5970_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1___boxed(
    mut v_constName_5972_: *mut crate::leanh::LeanObject,
    mut v___y_5973_: *mut crate::leanh::LeanObject,
    mut v___y_5974_: *mut crate::leanh::LeanObject,
    mut v___y_5975_: *mut crate::leanh::LeanObject,
    mut v___y_5976_: *mut crate::leanh::LeanObject,
    mut v___y_5977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5978_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(v_constName_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_);
    crate::leanh::lean_dec(v___y_5976_);
    crate::leanh::lean_dec_ref(v___y_5975_);
    crate::leanh::lean_dec(v___y_5974_);
    crate::leanh::lean_dec_ref(v___y_5973_);
    return v_res_5978_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2()
-> f64 {
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: f64 = 0.0;
    v___x_5982_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5983_ = lean_float_of_nat(v___x_5982_);
    return v___x_5983_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__4;
    v___x_5987_ = l_Lean_stringToMessageData(v___x_5986_);
    return v___x_5987_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(
    mut v_sz_5990_: usize,
    mut v_i_5991_: usize,
    mut v_bs_5992_: *mut crate::leanh::LeanObject,
    mut v___y_5993_: *mut crate::leanh::LeanObject,
    mut v___y_5994_: *mut crate::leanh::LeanObject,
    mut v___y_5995_: *mut crate::leanh::LeanObject,
    mut v___y_5996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5998_: u8 = 0;
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6005_: u8 = 0;
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: f64 = 0.0;
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: usize = 0;
    let mut v___x_6026_: usize = 0;
    let mut v___x_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6033_: u8 = 0;
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6037_: u8 = 0;
    let mut v_isSharedCheck_6038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5998_ = lean_usize_dec_lt(v_i_5991_, v_sz_5990_);
                if v___x_5998_ == 0 {
                    v___x_5999_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5999_, 0, v_bs_5992_);
                    return v___x_5999_;
                } else {
                    v_v_6000_ = lean_array_uget(v_bs_5992_, v_i_5991_);
                    v_fst_6001_ = crate::leanh::lean_ctor_get(v_v_6000_, 0);
                    v_snd_6002_ = crate::leanh::lean_ctor_get(v_v_6000_, 1);
                    v_isSharedCheck_6038_ = (!crate::leanh::lean_is_exclusive(v_v_6000_)) as u8;
                    if v_isSharedCheck_6038_ == 0 {
                        v___x_6004_ = v_v_6000_;
                        v_isShared_6005_ = v_isSharedCheck_6038_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6002_);
                        crate::leanh::lean_inc(v_fst_6001_);
                        crate::leanh::lean_dec(v_v_6000_);
                        v___x_6004_ = crate::leanh::lean_box(0);
                        v_isShared_6005_ = v_isSharedCheck_6038_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6006_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(v_fst_6001_, v___y_5993_, v___y_5994_, v___y_5995_, v___y_5996_);
                if crate::leanh::lean_obj_tag(v___x_6006_) == 0 {
                    v_a_6007_ = crate::leanh::lean_ctor_get(v___x_6006_, 0);
                    crate::leanh::lean_inc(v_a_6007_);
                    crate::leanh::lean_dec_ref_known(v___x_6006_, 1);
                    v___x_6008_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6009_ = lean_array_uset(v_bs_5992_, v_i_5991_, v___x_6008_);
                    v___x_6010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1;
                    v___x_6011_ = crate::leanh::lean_box(0);
                    v___x_6012_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2);
                    v___x_6013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3;
                    v___x_6014_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v___x_6014_, 0, v___x_6010_);
                    crate::leanh::lean_ctor_set(v___x_6014_, 1, v___x_6011_);
                    crate::leanh::lean_ctor_set(v___x_6014_, 2, v___x_6013_);
                    crate::leanh::lean_ctor_set_float(
                        v___x_6014_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_6012_,
                    );
                    crate::leanh::lean_ctor_set_float(
                        v___x_6014_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_6012_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6014_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v___x_5998_,
                    );
                    v___x_6015_ = l_Lean_MessageData_ofConst(v_a_6007_);
                    v___x_6016_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5);
                    if v_isShared_6005_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6004_, 7);
                        crate::leanh::lean_ctor_set(v___x_6004_, 1, v___x_6016_);
                        crate::leanh::lean_ctor_set(v___x_6004_, 0, v___x_6015_);
                        v___x_6018_ = v___x_6004_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6029_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6029_, 0, v___x_6015_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6029_, 1, v___x_6016_);
                        v___x_6018_ = v_reuseFailAlloc_6029_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6004_);
                    crate::leanh::lean_dec(v_snd_6002_);
                    crate::leanh::lean_dec_ref(v_bs_5992_);
                    v_a_6030_ = crate::leanh::lean_ctor_get(v___x_6006_, 0);
                    v_isSharedCheck_6037_ = (!crate::leanh::lean_is_exclusive(v___x_6006_)) as u8;
                    if v_isSharedCheck_6037_ == 0 {
                        v___x_6032_ = v___x_6006_;
                        v_isShared_6033_ = v_isSharedCheck_6037_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6030_);
                        crate::leanh::lean_dec(v___x_6006_);
                        v___x_6032_ = crate::leanh::lean_box(0);
                        v_isShared_6033_ = v_isSharedCheck_6037_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6019_ = l_Nat_reprFast(v_snd_6002_);
                v___x_6020_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6020_, 0, v___x_6019_);
                v___x_6021_ = l_Lean_MessageData_ofFormat(v___x_6020_);
                v___x_6022_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6022_, 0, v___x_6018_);
                crate::leanh::lean_ctor_set(v___x_6022_, 1, v___x_6021_);
                v___x_6023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__6;
                v___x_6024_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6024_, 0, v___x_6014_);
                crate::leanh::lean_ctor_set(v___x_6024_, 1, v___x_6022_);
                crate::leanh::lean_ctor_set(v___x_6024_, 2, v___x_6023_);
                v___x_6025_ = 1usize;
                v___x_6026_ = lean_usize_add(v_i_5991_, v___x_6025_);
                v___x_6027_ = lean_array_uset(v_bs_x27_6009_, v_i_5991_, v___x_6024_);
                v_i_5991_ = v___x_6026_;
                v_bs_5992_ = v___x_6027_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_6033_ == 0 {
                    v___x_6035_ = v___x_6032_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6036_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6036_, 0, v_a_6030_);
                    v___x_6035_ = v_reuseFailAlloc_6036_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___boxed(
    mut v_sz_6039_: *mut crate::leanh::LeanObject,
    mut v_i_6040_: *mut crate::leanh::LeanObject,
    mut v_bs_6041_: *mut crate::leanh::LeanObject,
    mut v___y_6042_: *mut crate::leanh::LeanObject,
    mut v___y_6043_: *mut crate::leanh::LeanObject,
    mut v___y_6044_: *mut crate::leanh::LeanObject,
    mut v___y_6045_: *mut crate::leanh::LeanObject,
    mut v___y_6046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6047_: usize = 0;
    let mut v_i_boxed_6048_: usize = 0;
    let mut v_res_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6047_ = crate::leanh::lean_unbox_usize(v_sz_6039_);
    crate::leanh::lean_dec(v_sz_6039_);
    v_i_boxed_6048_ = crate::leanh::lean_unbox_usize(v_i_6040_);
    crate::leanh::lean_dec(v_i_6040_);
    v_res_6049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(v_sz_boxed_6047_, v_i_boxed_6048_, v_bs_6041_, v___y_6042_, v___y_6043_, v___y_6044_, v___y_6045_);
    crate::leanh::lean_dec(v___y_6045_);
    crate::leanh::lean_dec_ref(v___y_6044_);
    crate::leanh::lean_dec(v___y_6043_);
    crate::leanh::lean_dec_ref(v___y_6042_);
    return v_res_6049_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: u8 = 0;
    let mut v___x_6052_: f64 = 0.0;
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3;
    v___x_6051_ = 1;
    v___x_6052_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2);
    v___x_6053_ = crate::leanh::lean_box(0);
    v___x_6054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1;
    v___x_6055_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_6055_, 0, v___x_6054_);
    crate::leanh::lean_ctor_set(v___x_6055_, 1, v___x_6053_);
    crate::leanh::lean_ctor_set(v___x_6055_, 2, v___x_6050_);
    crate::leanh::lean_ctor_set_float(
        v___x_6055_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_6052_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_6055_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_6052_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_6055_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_6051_,
    );
    return v___x_6055_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6059_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__2;
    v___x_6060_ = l_Lean_MessageData_ofFormat(v___x_6059_);
    return v___x_6060_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(
    mut v_thms_6061_: *mut crate::leanh::LeanObject,
    mut v_a_6062_: *mut crate::leanh::LeanObject,
    mut v_a_6063_: *mut crate::leanh::LeanObject,
    mut v_a_6064_: *mut crate::leanh::LeanObject,
    mut v_a_6065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6071_: usize = 0;
    let mut v___x_6072_: usize = 0;
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6077_: u8 = 0;
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6084_: u8 = 0;
    let mut v_a_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6088_: u8 = 0;
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6092_: u8 = 0;
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: u8 = 0;
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: u8 = 0;
    let mut v___x_6106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6067_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_thms_6061_);
                v___x_6068_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6093_ = lean_array_get_size(v___x_6067_);
                v_data_6094_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(v___x_6067_, v___x_6068_, v___x_6093_);
                crate::leanh::lean_dec_ref(v___x_6067_);
                v___x_6095_ = lean_array_get_size(v_data_6094_);
                v___x_6100_ = lean_nat_dec_eq(v___x_6095_, v___x_6068_);
                if v___x_6100_ == 0 {
                    v___x_6101_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6102_ = lean_nat_sub(v___x_6095_, v___x_6101_);
                    v___x_6106_ = lean_nat_dec_le(v___x_6068_, v___x_6102_);
                    if v___x_6106_ == 0 {
                        crate::leanh::lean_inc(v___x_6102_);
                        v___y_6104_ = v___x_6102_;
                        state = 7;
                        continue;
                    } else {
                        v___y_6104_ = v___x_6068_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___y_6070_ = v_data_6094_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_sz_6071_ = lean_array_size(v___y_6070_);
                v___x_6072_ = 0usize;
                v___x_6073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(v_sz_6071_, v___x_6072_, v___y_6070_, v_a_6062_, v_a_6063_, v_a_6064_, v_a_6065_);
                if crate::leanh::lean_obj_tag(v___x_6073_) == 0 {
                    v_a_6074_ = crate::leanh::lean_ctor_get(v___x_6073_, 0);
                    v_isSharedCheck_6084_ = (!crate::leanh::lean_is_exclusive(v___x_6073_)) as u8;
                    if v_isSharedCheck_6084_ == 0 {
                        v___x_6076_ = v___x_6073_;
                        v_isShared_6077_ = v_isSharedCheck_6084_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6074_);
                        crate::leanh::lean_dec(v___x_6073_);
                        v___x_6076_ = crate::leanh::lean_box(0);
                        v_isShared_6077_ = v_isSharedCheck_6084_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6085_ = crate::leanh::lean_ctor_get(v___x_6073_, 0);
                    v_isSharedCheck_6092_ = (!crate::leanh::lean_is_exclusive(v___x_6073_)) as u8;
                    if v_isSharedCheck_6092_ == 0 {
                        v___x_6087_ = v___x_6073_;
                        v_isShared_6088_ = v_isSharedCheck_6092_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6085_);
                        crate::leanh::lean_dec(v___x_6073_);
                        v___x_6087_ = crate::leanh::lean_box(0);
                        v_isShared_6088_ = v_isSharedCheck_6092_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6078_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0);
                v___x_6079_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3);
                v___x_6080_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6080_, 0, v___x_6078_);
                crate::leanh::lean_ctor_set(v___x_6080_, 1, v___x_6079_);
                crate::leanh::lean_ctor_set(v___x_6080_, 2, v_a_6074_);
                if v_isShared_6077_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6076_, 0, v___x_6080_);
                    v___x_6082_ = v___x_6076_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6083_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6083_, 0, v___x_6080_);
                    v___x_6082_ = v_reuseFailAlloc_6083_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6082_;
            }
            4 => {
                if v_isShared_6088_ == 0 {
                    v___x_6090_ = v___x_6087_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6091_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6091_, 0, v_a_6085_);
                    v___x_6090_ = v_reuseFailAlloc_6091_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6090_;
            }
            6 => {
                v___x_6099_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v___x_6095_, v_data_6094_, v___y_6097_, v___y_6098_);
                crate::leanh::lean_dec(v___y_6098_);
                v___y_6070_ = v___x_6099_;
                state = 1;
                continue;
            }
            7 => {
                v___x_6105_ = lean_nat_dec_le(v___y_6104_, v___x_6102_);
                if v___x_6105_ == 0 {
                    crate::leanh::lean_dec(v___x_6102_);
                    crate::leanh::lean_inc(v___y_6104_);
                    v___y_6097_ = v___y_6104_;
                    v___y_6098_ = v___y_6104_;
                    state = 6;
                    continue;
                } else {
                    v___y_6097_ = v___y_6104_;
                    v___y_6098_ = v___x_6102_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___boxed(
    mut v_thms_6107_: *mut crate::leanh::LeanObject,
    mut v_a_6108_: *mut crate::leanh::LeanObject,
    mut v_a_6109_: *mut crate::leanh::LeanObject,
    mut v_a_6110_: *mut crate::leanh::LeanObject,
    mut v_a_6111_: *mut crate::leanh::LeanObject,
    mut v_a_6112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6113_ =
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(
            v_thms_6107_,
            v_a_6108_,
            v_a_6109_,
            v_a_6110_,
            v_a_6111_,
        );
    crate::leanh::lean_dec(v_a_6111_);
    crate::leanh::lean_dec_ref(v_a_6110_);
    crate::leanh::lean_dec(v_a_6109_);
    crate::leanh::lean_dec_ref(v_a_6108_);
    crate::leanh::lean_dec_ref(v_thms_6107_);
    return v_res_6113_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0(
    mut v_00_u03b2_6114_: *mut crate::leanh::LeanObject,
    mut v_m_6115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6116_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_m_6115_);
    return v___x_6116_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___boxed(
    mut v_00_u03b2_6117_: *mut crate::leanh::LeanObject,
    mut v_m_6118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6119_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0(v_00_u03b2_6117_, v_m_6118_);
    crate::leanh::lean_dec_ref(v_m_6118_);
    return v_res_6119_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4(
    mut v_n_6120_: *mut crate::leanh::LeanObject,
    mut v_as_6121_: *mut crate::leanh::LeanObject,
    mut v_lo_6122_: *mut crate::leanh::LeanObject,
    mut v_hi_6123_: *mut crate::leanh::LeanObject,
    mut v_w_6124_: *mut crate::leanh::LeanObject,
    mut v_hlo_6125_: *mut crate::leanh::LeanObject,
    mut v_hhi_6126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6127_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_6120_, v_as_6121_, v_lo_6122_, v_hi_6123_);
    return v___x_6127_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___boxed(
    mut v_n_6128_: *mut crate::leanh::LeanObject,
    mut v_as_6129_: *mut crate::leanh::LeanObject,
    mut v_lo_6130_: *mut crate::leanh::LeanObject,
    mut v_hi_6131_: *mut crate::leanh::LeanObject,
    mut v_w_6132_: *mut crate::leanh::LeanObject,
    mut v_hlo_6133_: *mut crate::leanh::LeanObject,
    mut v_hhi_6134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6135_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4(v_n_6128_, v_as_6129_, v_lo_6130_, v_hi_6131_, v_w_6132_, v_hlo_6133_, v_hhi_6134_);
    crate::leanh::lean_dec(v_hi_6131_);
    crate::leanh::lean_dec(v_n_6128_);
    return v_res_6135_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0(
    mut v_00_u03c3_6136_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6137_: *mut crate::leanh::LeanObject,
    mut v_map_6138_: *mut crate::leanh::LeanObject,
    mut v_f_6139_: *mut crate::leanh::LeanObject,
    mut v_init_6140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6141_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_map_6138_, v_f_6139_, v_init_6140_);
    return v___x_6141_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___boxed(
    mut v_00_u03c3_6142_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6143_: *mut crate::leanh::LeanObject,
    mut v_map_6144_: *mut crate::leanh::LeanObject,
    mut v_f_6145_: *mut crate::leanh::LeanObject,
    mut v_init_6146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6147_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0(v_00_u03c3_6142_, v_00_u03b2_6143_, v_map_6144_, v_f_6145_, v_init_6146_);
    crate::leanh::lean_dec_ref(v_map_6144_);
    return v_res_6147_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8(
    mut v_n_6148_: *mut crate::leanh::LeanObject,
    mut v_lo_6149_: *mut crate::leanh::LeanObject,
    mut v_hi_6150_: *mut crate::leanh::LeanObject,
    mut v_hhi_6151_: *mut crate::leanh::LeanObject,
    mut v_pivot_6152_: *mut crate::leanh::LeanObject,
    mut v_as_6153_: *mut crate::leanh::LeanObject,
    mut v_i_6154_: *mut crate::leanh::LeanObject,
    mut v_k_6155_: *mut crate::leanh::LeanObject,
    mut v_ilo_6156_: *mut crate::leanh::LeanObject,
    mut v_ik_6157_: *mut crate::leanh::LeanObject,
    mut v_w_6158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6159_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_6150_, v_pivot_6152_, v_as_6153_, v_i_6154_, v_k_6155_);
    return v___x_6159_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___boxed(
    mut v_n_6160_: *mut crate::leanh::LeanObject,
    mut v_lo_6161_: *mut crate::leanh::LeanObject,
    mut v_hi_6162_: *mut crate::leanh::LeanObject,
    mut v_hhi_6163_: *mut crate::leanh::LeanObject,
    mut v_pivot_6164_: *mut crate::leanh::LeanObject,
    mut v_as_6165_: *mut crate::leanh::LeanObject,
    mut v_i_6166_: *mut crate::leanh::LeanObject,
    mut v_k_6167_: *mut crate::leanh::LeanObject,
    mut v_ilo_6168_: *mut crate::leanh::LeanObject,
    mut v_ik_6169_: *mut crate::leanh::LeanObject,
    mut v_w_6170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6171_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8(v_n_6160_, v_lo_6161_, v_hi_6162_, v_hhi_6163_, v_pivot_6164_, v_as_6165_, v_i_6166_, v_k_6167_, v_ilo_6168_, v_ik_6169_, v_w_6170_);
    crate::leanh::lean_dec_ref(v_pivot_6164_);
    crate::leanh::lean_dec(v_hi_6162_);
    crate::leanh::lean_dec(v_lo_6161_);
    crate::leanh::lean_dec(v_n_6160_);
    return v_res_6171_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg(
    mut v_map_6172_: *mut crate::leanh::LeanObject,
    mut v_f_6173_: *mut crate::leanh::LeanObject,
    mut v_init_6174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6175_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_6173_, v_map_6172_, v_init_6174_);
    return v___x_6175_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_map_6176_: *mut crate::leanh::LeanObject,
    mut v_f_6177_: *mut crate::leanh::LeanObject,
    mut v_init_6178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6179_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg(v_map_6176_, v_f_6177_, v_init_6178_);
    crate::leanh::lean_dec_ref(v_map_6176_);
    return v_res_6179_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1(
    mut v_00_u03c3_6180_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6181_: *mut crate::leanh::LeanObject,
    mut v_map_6182_: *mut crate::leanh::LeanObject,
    mut v_f_6183_: *mut crate::leanh::LeanObject,
    mut v_init_6184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6185_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_6183_, v_map_6182_, v_init_6184_);
    return v___x_6185_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03c3_6186_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6187_: *mut crate::leanh::LeanObject,
    mut v_map_6188_: *mut crate::leanh::LeanObject,
    mut v_f_6189_: *mut crate::leanh::LeanObject,
    mut v_init_6190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6191_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1(v_00_u03c3_6186_, v_00_u03b2_6187_, v_map_6188_, v_f_6189_, v_init_6190_);
    crate::leanh::lean_dec_ref(v_map_6188_);
    return v_res_6191_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4(
    mut v_00_u03b1_6192_: *mut crate::leanh::LeanObject,
    mut v_constName_6193_: *mut crate::leanh::LeanObject,
    mut v___y_6194_: *mut crate::leanh::LeanObject,
    mut v___y_6195_: *mut crate::leanh::LeanObject,
    mut v___y_6196_: *mut crate::leanh::LeanObject,
    mut v___y_6197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6199_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_6193_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_);
    return v___x_6199_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_6200_: *mut crate::leanh::LeanObject,
    mut v_constName_6201_: *mut crate::leanh::LeanObject,
    mut v___y_6202_: *mut crate::leanh::LeanObject,
    mut v___y_6203_: *mut crate::leanh::LeanObject,
    mut v___y_6204_: *mut crate::leanh::LeanObject,
    mut v___y_6205_: *mut crate::leanh::LeanObject,
    mut v___y_6206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6207_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4(v_00_u03b1_6200_, v_constName_6201_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_);
    crate::leanh::lean_dec(v___y_6205_);
    crate::leanh::lean_dec_ref(v___y_6204_);
    crate::leanh::lean_dec(v___y_6203_);
    crate::leanh::lean_dec_ref(v___y_6202_);
    return v_res_6207_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6(
    mut v_00_u03c3_6208_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6209_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6210_: *mut crate::leanh::LeanObject,
    mut v_f_6211_: *mut crate::leanh::LeanObject,
    mut v_x_6212_: *mut crate::leanh::LeanObject,
    mut v_x_6213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6214_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_6211_, v_x_6212_, v_x_6213_);
    return v___x_6214_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___boxed(
    mut v_00_u03c3_6215_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6216_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6217_: *mut crate::leanh::LeanObject,
    mut v_f_6218_: *mut crate::leanh::LeanObject,
    mut v_x_6219_: *mut crate::leanh::LeanObject,
    mut v_x_6220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6221_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6(v_00_u03c3_6215_, v_00_u03b1_6216_, v_00_u03b2_6217_, v_f_6218_, v_x_6219_, v_x_6220_);
    crate::leanh::lean_dec_ref(v_x_6219_);
    return v_res_6221_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9(
    mut v_00_u03b1_6222_: *mut crate::leanh::LeanObject,
    mut v_ref_6223_: *mut crate::leanh::LeanObject,
    mut v_constName_6224_: *mut crate::leanh::LeanObject,
    mut v___y_6225_: *mut crate::leanh::LeanObject,
    mut v___y_6226_: *mut crate::leanh::LeanObject,
    mut v___y_6227_: *mut crate::leanh::LeanObject,
    mut v___y_6228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6230_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_6223_, v_constName_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_);
    return v___x_6230_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___boxed(
    mut v_00_u03b1_6231_: *mut crate::leanh::LeanObject,
    mut v_ref_6232_: *mut crate::leanh::LeanObject,
    mut v_constName_6233_: *mut crate::leanh::LeanObject,
    mut v___y_6234_: *mut crate::leanh::LeanObject,
    mut v___y_6235_: *mut crate::leanh::LeanObject,
    mut v___y_6236_: *mut crate::leanh::LeanObject,
    mut v___y_6237_: *mut crate::leanh::LeanObject,
    mut v___y_6238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6239_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9(v_00_u03b1_6231_, v_ref_6232_, v_constName_6233_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_);
    crate::leanh::lean_dec(v___y_6237_);
    crate::leanh::lean_dec_ref(v___y_6236_);
    crate::leanh::lean_dec(v___y_6235_);
    crate::leanh::lean_dec_ref(v___y_6234_);
    crate::leanh::lean_dec(v_ref_6232_);
    return v_res_6239_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11(
    mut v_00_u03b1_6240_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6241_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6242_: *mut crate::leanh::LeanObject,
    mut v_f_6243_: *mut crate::leanh::LeanObject,
    mut v_as_6244_: *mut crate::leanh::LeanObject,
    mut v_i_6245_: usize,
    mut v_stop_6246_: usize,
    mut v_b_6247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_6243_, v_as_6244_, v_i_6245_, v_stop_6246_, v_b_6247_);
    return v___x_6248_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___boxed(
    mut v_00_u03b1_6249_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6250_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6251_: *mut crate::leanh::LeanObject,
    mut v_f_6252_: *mut crate::leanh::LeanObject,
    mut v_as_6253_: *mut crate::leanh::LeanObject,
    mut v_i_6254_: *mut crate::leanh::LeanObject,
    mut v_stop_6255_: *mut crate::leanh::LeanObject,
    mut v_b_6256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6257_: usize = 0;
    let mut v_stop_boxed_6258_: usize = 0;
    let mut v_res_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6257_ = crate::leanh::lean_unbox_usize(v_i_6254_);
    crate::leanh::lean_dec(v_i_6254_);
    v_stop_boxed_6258_ = crate::leanh::lean_unbox_usize(v_stop_6255_);
    crate::leanh::lean_dec(v_stop_6255_);
    v_res_6259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11(v_00_u03b1_6249_, v_00_u03b2_6250_, v_00_u03c3_6251_, v_f_6252_, v_as_6253_, v_i_boxed_6257_, v_stop_boxed_6258_, v_b_6256_);
    crate::leanh::lean_dec_ref(v_as_6253_);
    return v_res_6259_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12(
    mut v_00_u03c3_6260_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6261_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6262_: *mut crate::leanh::LeanObject,
    mut v_f_6263_: *mut crate::leanh::LeanObject,
    mut v_keys_6264_: *mut crate::leanh::LeanObject,
    mut v_vals_6265_: *mut crate::leanh::LeanObject,
    mut v_heq_6266_: *mut crate::leanh::LeanObject,
    mut v_i_6267_: *mut crate::leanh::LeanObject,
    mut v_acc_6268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_6263_, v_keys_6264_, v_vals_6265_, v_i_6267_, v_acc_6268_);
    return v___x_6269_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___boxed(
    mut v_00_u03c3_6270_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6271_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6272_: *mut crate::leanh::LeanObject,
    mut v_f_6273_: *mut crate::leanh::LeanObject,
    mut v_keys_6274_: *mut crate::leanh::LeanObject,
    mut v_vals_6275_: *mut crate::leanh::LeanObject,
    mut v_heq_6276_: *mut crate::leanh::LeanObject,
    mut v_i_6277_: *mut crate::leanh::LeanObject,
    mut v_acc_6278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12(v_00_u03c3_6270_, v_00_u03b1_6271_, v_00_u03b2_6272_, v_f_6273_, v_keys_6274_, v_vals_6275_, v_heq_6276_, v_i_6277_, v_acc_6278_);
    crate::leanh::lean_dec_ref(v_vals_6275_);
    crate::leanh::lean_dec_ref(v_keys_6274_);
    return v_res_6279_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15(
    mut v_00_u03b1_6280_: *mut crate::leanh::LeanObject,
    mut v_ref_6281_: *mut crate::leanh::LeanObject,
    mut v_msg_6282_: *mut crate::leanh::LeanObject,
    mut v_declHint_6283_: *mut crate::leanh::LeanObject,
    mut v___y_6284_: *mut crate::leanh::LeanObject,
    mut v___y_6285_: *mut crate::leanh::LeanObject,
    mut v___y_6286_: *mut crate::leanh::LeanObject,
    mut v___y_6287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6289_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_6281_, v_msg_6282_, v_declHint_6283_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_);
    return v___x_6289_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___boxed(
    mut v_00_u03b1_6290_: *mut crate::leanh::LeanObject,
    mut v_ref_6291_: *mut crate::leanh::LeanObject,
    mut v_msg_6292_: *mut crate::leanh::LeanObject,
    mut v_declHint_6293_: *mut crate::leanh::LeanObject,
    mut v___y_6294_: *mut crate::leanh::LeanObject,
    mut v___y_6295_: *mut crate::leanh::LeanObject,
    mut v___y_6296_: *mut crate::leanh::LeanObject,
    mut v___y_6297_: *mut crate::leanh::LeanObject,
    mut v___y_6298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6299_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15(v_00_u03b1_6290_, v_ref_6291_, v_msg_6292_, v_declHint_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_);
    crate::leanh::lean_dec(v___y_6297_);
    crate::leanh::lean_dec_ref(v___y_6296_);
    crate::leanh::lean_dec(v___y_6295_);
    crate::leanh::lean_dec_ref(v___y_6294_);
    crate::leanh::lean_dec(v_ref_6291_);
    return v_res_6299_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17(
    mut v_msg_6300_: *mut crate::leanh::LeanObject,
    mut v_declHint_6301_: *mut crate::leanh::LeanObject,
    mut v___y_6302_: *mut crate::leanh::LeanObject,
    mut v___y_6303_: *mut crate::leanh::LeanObject,
    mut v___y_6304_: *mut crate::leanh::LeanObject,
    mut v___y_6305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6307_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_6300_, v_declHint_6301_, v___y_6305_);
    return v___x_6307_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___boxed(
    mut v_msg_6308_: *mut crate::leanh::LeanObject,
    mut v_declHint_6309_: *mut crate::leanh::LeanObject,
    mut v___y_6310_: *mut crate::leanh::LeanObject,
    mut v___y_6311_: *mut crate::leanh::LeanObject,
    mut v___y_6312_: *mut crate::leanh::LeanObject,
    mut v___y_6313_: *mut crate::leanh::LeanObject,
    mut v___y_6314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6315_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17(v_msg_6308_, v_declHint_6309_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_);
    crate::leanh::lean_dec(v___y_6313_);
    crate::leanh::lean_dec_ref(v___y_6312_);
    crate::leanh::lean_dec(v___y_6311_);
    crate::leanh::lean_dec_ref(v___y_6310_);
    return v_res_6315_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17(
    mut v_00_u03b1_6316_: *mut crate::leanh::LeanObject,
    mut v_ref_6317_: *mut crate::leanh::LeanObject,
    mut v_msg_6318_: *mut crate::leanh::LeanObject,
    mut v___y_6319_: *mut crate::leanh::LeanObject,
    mut v___y_6320_: *mut crate::leanh::LeanObject,
    mut v___y_6321_: *mut crate::leanh::LeanObject,
    mut v___y_6322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6324_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_6317_, v_msg_6318_, v___y_6319_, v___y_6320_, v___y_6321_, v___y_6322_);
    return v___x_6324_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___boxed(
    mut v_00_u03b1_6325_: *mut crate::leanh::LeanObject,
    mut v_ref_6326_: *mut crate::leanh::LeanObject,
    mut v_msg_6327_: *mut crate::leanh::LeanObject,
    mut v___y_6328_: *mut crate::leanh::LeanObject,
    mut v___y_6329_: *mut crate::leanh::LeanObject,
    mut v___y_6330_: *mut crate::leanh::LeanObject,
    mut v___y_6331_: *mut crate::leanh::LeanObject,
    mut v___y_6332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6333_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17(v_00_u03b1_6325_, v_ref_6326_, v_msg_6327_, v___y_6328_, v___y_6329_, v___y_6330_, v___y_6331_);
    crate::leanh::lean_dec(v___y_6331_);
    crate::leanh::lean_dec_ref(v___y_6330_);
    crate::leanh::lean_dec(v___y_6329_);
    crate::leanh::lean_dec_ref(v___y_6328_);
    crate::leanh::lean_dec(v_ref_6326_);
    return v_res_6333_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19(
    mut v_00_u03b1_6334_: *mut crate::leanh::LeanObject,
    mut v_msg_6335_: *mut crate::leanh::LeanObject,
    mut v___y_6336_: *mut crate::leanh::LeanObject,
    mut v___y_6337_: *mut crate::leanh::LeanObject,
    mut v___y_6338_: *mut crate::leanh::LeanObject,
    mut v___y_6339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6341_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_6335_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_);
    return v___x_6341_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___boxed(
    mut v_00_u03b1_6342_: *mut crate::leanh::LeanObject,
    mut v_msg_6343_: *mut crate::leanh::LeanObject,
    mut v___y_6344_: *mut crate::leanh::LeanObject,
    mut v___y_6345_: *mut crate::leanh::LeanObject,
    mut v___y_6346_: *mut crate::leanh::LeanObject,
    mut v___y_6347_: *mut crate::leanh::LeanObject,
    mut v___y_6348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6349_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19(v_00_u03b1_6342_, v_msg_6343_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_);
    crate::leanh::lean_dec(v___y_6347_);
    crate::leanh::lean_dec_ref(v___y_6346_);
    crate::leanh::lean_dec(v___y_6345_);
    crate::leanh::lean_dec_ref(v___y_6344_);
    return v_res_6349_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0(
    mut v_k_6350_: *mut crate::leanh::LeanObject,
    mut v_b_6351_: *mut crate::leanh::LeanObject,
    mut v_c_6352_: *mut crate::leanh::LeanObject,
    mut v___y_6353_: *mut crate::leanh::LeanObject,
    mut v___y_6354_: *mut crate::leanh::LeanObject,
    mut v___y_6355_: *mut crate::leanh::LeanObject,
    mut v___y_6356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_6356_);
    crate::leanh::lean_inc_ref(v___y_6355_);
    crate::leanh::lean_inc(v___y_6354_);
    crate::leanh::lean_inc_ref(v___y_6353_);
    v___x_6358_ = crate::leanh::lean_apply_7(
        v_k_6350_,
        v_b_6351_,
        v_c_6352_,
        v___y_6353_,
        v___y_6354_,
        v___y_6355_,
        v___y_6356_,
        crate::leanh::lean_box(0),
    );
    return v___x_6358_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0___boxed(
    mut v_k_6359_: *mut crate::leanh::LeanObject,
    mut v_b_6360_: *mut crate::leanh::LeanObject,
    mut v_c_6361_: *mut crate::leanh::LeanObject,
    mut v___y_6362_: *mut crate::leanh::LeanObject,
    mut v___y_6363_: *mut crate::leanh::LeanObject,
    mut v___y_6364_: *mut crate::leanh::LeanObject,
    mut v___y_6365_: *mut crate::leanh::LeanObject,
    mut v___y_6366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6367_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0(v_k_6359_, v_b_6360_, v_c_6361_, v___y_6362_, v___y_6363_, v___y_6364_, v___y_6365_);
    crate::leanh::lean_dec(v___y_6365_);
    crate::leanh::lean_dec_ref(v___y_6364_);
    crate::leanh::lean_dec(v___y_6363_);
    crate::leanh::lean_dec_ref(v___y_6362_);
    return v_res_6367_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(
    mut v_type_6368_: *mut crate::leanh::LeanObject,
    mut v_k_6369_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_6370_: u8,
    mut v___y_6371_: *mut crate::leanh::LeanObject,
    mut v___y_6372_: *mut crate::leanh::LeanObject,
    mut v___y_6373_: *mut crate::leanh::LeanObject,
    mut v___y_6374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: u8 = 0;
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6383_: u8 = 0;
    let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6387_: u8 = 0;
    let mut v_a_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6391_: u8 = 0;
    let mut v___x_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6376_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_6376_, 0, v_k_6369_);
                v___x_6377_ = 0;
                v___x_6378_ = crate::leanh::lean_box(0);
                v___x_6379_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        crate::leanh::lean_box(0),
                        v___x_6377_,
                        v___x_6378_,
                        v_type_6368_,
                        v___f_6376_,
                        v_cleanupAnnotations_6370_,
                        v___x_6377_,
                        v___y_6371_,
                        v___y_6372_,
                        v___y_6373_,
                        v___y_6374_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6379_) == 0 {
                    v_a_6380_ = crate::leanh::lean_ctor_get(v___x_6379_, 0);
                    v_isSharedCheck_6387_ = (!crate::leanh::lean_is_exclusive(v___x_6379_)) as u8;
                    if v_isSharedCheck_6387_ == 0 {
                        v___x_6382_ = v___x_6379_;
                        v_isShared_6383_ = v_isSharedCheck_6387_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6380_);
                        crate::leanh::lean_dec(v___x_6379_);
                        v___x_6382_ = crate::leanh::lean_box(0);
                        v_isShared_6383_ = v_isSharedCheck_6387_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6388_ = crate::leanh::lean_ctor_get(v___x_6379_, 0);
                    v_isSharedCheck_6395_ = (!crate::leanh::lean_is_exclusive(v___x_6379_)) as u8;
                    if v_isSharedCheck_6395_ == 0 {
                        v___x_6390_ = v___x_6379_;
                        v_isShared_6391_ = v_isSharedCheck_6395_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6388_);
                        crate::leanh::lean_dec(v___x_6379_);
                        v___x_6390_ = crate::leanh::lean_box(0);
                        v_isShared_6391_ = v_isSharedCheck_6395_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6383_ == 0 {
                    v___x_6385_ = v___x_6382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6386_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 0, v_a_6380_);
                    v___x_6385_ = v_reuseFailAlloc_6386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6385_;
            }
            3 => {
                if v_isShared_6391_ == 0 {
                    v___x_6393_ = v___x_6390_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6394_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6394_, 0, v_a_6388_);
                    v___x_6393_ = v_reuseFailAlloc_6394_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6393_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___boxed(
    mut v_type_6396_: *mut crate::leanh::LeanObject,
    mut v_k_6397_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_6398_: *mut crate::leanh::LeanObject,
    mut v___y_6399_: *mut crate::leanh::LeanObject,
    mut v___y_6400_: *mut crate::leanh::LeanObject,
    mut v___y_6401_: *mut crate::leanh::LeanObject,
    mut v___y_6402_: *mut crate::leanh::LeanObject,
    mut v___y_6403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_6404_: u8 = 0;
    let mut v_res_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_6404_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_6398_) as u8);
    v_res_6405_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v_type_6396_, v_k_6397_, v_cleanupAnnotations_boxed_6404_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_);
    crate::leanh::lean_dec(v___y_6402_);
    crate::leanh::lean_dec_ref(v___y_6401_);
    crate::leanh::lean_dec(v___y_6400_);
    crate::leanh::lean_dec_ref(v___y_6399_);
    return v_res_6405_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2(
    mut v_00_u03b1_6406_: *mut crate::leanh::LeanObject,
    mut v_type_6407_: *mut crate::leanh::LeanObject,
    mut v_k_6408_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_6409_: u8,
    mut v___y_6410_: *mut crate::leanh::LeanObject,
    mut v___y_6411_: *mut crate::leanh::LeanObject,
    mut v___y_6412_: *mut crate::leanh::LeanObject,
    mut v___y_6413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6415_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v_type_6407_, v_k_6408_, v_cleanupAnnotations_6409_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_);
    return v___x_6415_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___boxed(
    mut v_00_u03b1_6416_: *mut crate::leanh::LeanObject,
    mut v_type_6417_: *mut crate::leanh::LeanObject,
    mut v_k_6418_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_6419_: *mut crate::leanh::LeanObject,
    mut v___y_6420_: *mut crate::leanh::LeanObject,
    mut v___y_6421_: *mut crate::leanh::LeanObject,
    mut v___y_6422_: *mut crate::leanh::LeanObject,
    mut v___y_6423_: *mut crate::leanh::LeanObject,
    mut v___y_6424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_6425_: u8 = 0;
    let mut v_res_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_6425_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_6419_) as u8);
    v_res_6426_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2(v_00_u03b1_6416_, v_type_6417_, v_k_6418_, v_cleanupAnnotations_boxed_6425_, v___y_6420_, v___y_6421_, v___y_6422_, v___y_6423_);
    crate::leanh::lean_dec(v___y_6423_);
    crate::leanh::lean_dec_ref(v___y_6422_);
    crate::leanh::lean_dec(v___y_6421_);
    crate::leanh::lean_dec_ref(v___y_6420_);
    return v_res_6426_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6430_ = crate::leanh::lean_box(0);
    v___x_6431_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__1;
    v___x_6432_ = l_Lean_mkConst(v___x_6431_, v___x_6430_);
    return v___x_6432_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6433_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2);
    v___x_6434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6434_, 0, v___x_6433_);
    return v___x_6434_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0(
    mut v_x_6435_: *mut crate::leanh::LeanObject,
    mut v___y_6436_: *mut crate::leanh::LeanObject,
    mut v___y_6437_: *mut crate::leanh::LeanObject,
    mut v___y_6438_: *mut crate::leanh::LeanObject,
    mut v___y_6439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: u8 = 0;
    let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6448_: u8 = 0;
    let mut v___x_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6453_: u8 = 0;
    let mut v_a_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6457_: u8 = 0;
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6441_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3);
                v___x_6442_ = 0;
                v___x_6443_ = crate::leanh::lean_box(0);
                v___x_6444_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_6441_,
                    v___x_6442_,
                    v___x_6443_,
                    v___y_6436_,
                    v___y_6437_,
                    v___y_6438_,
                    v___y_6439_,
                );
                if crate::leanh::lean_obj_tag(v___x_6444_) == 0 {
                    v_a_6445_ = crate::leanh::lean_ctor_get(v___x_6444_, 0);
                    v_isSharedCheck_6453_ = (!crate::leanh::lean_is_exclusive(v___x_6444_)) as u8;
                    if v_isSharedCheck_6453_ == 0 {
                        v___x_6447_ = v___x_6444_;
                        v_isShared_6448_ = v_isSharedCheck_6453_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6445_);
                        crate::leanh::lean_dec(v___x_6444_);
                        v___x_6447_ = crate::leanh::lean_box(0);
                        v_isShared_6448_ = v_isSharedCheck_6453_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6454_ = crate::leanh::lean_ctor_get(v___x_6444_, 0);
                    v_isSharedCheck_6461_ = (!crate::leanh::lean_is_exclusive(v___x_6444_)) as u8;
                    if v_isSharedCheck_6461_ == 0 {
                        v___x_6456_ = v___x_6444_;
                        v_isShared_6457_ = v_isSharedCheck_6461_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6454_);
                        crate::leanh::lean_dec(v___x_6444_);
                        v___x_6456_ = crate::leanh::lean_box(0);
                        v_isShared_6457_ = v_isSharedCheck_6461_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6449_ = l_Lean_Expr_mvarId_x21(v_a_6445_);
                crate::leanh::lean_dec(v_a_6445_);
                if v_isShared_6448_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6447_, 0, v___x_6449_);
                    v___x_6451_ = v___x_6447_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6452_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6452_, 0, v___x_6449_);
                    v___x_6451_ = v_reuseFailAlloc_6452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6451_;
            }
            3 => {
                if v_isShared_6457_ == 0 {
                    v___x_6459_ = v___x_6456_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6460_, 0, v_a_6454_);
                    v___x_6459_ = v_reuseFailAlloc_6460_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6459_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___boxed(
    mut v_x_6462_: *mut crate::leanh::LeanObject,
    mut v___y_6463_: *mut crate::leanh::LeanObject,
    mut v___y_6464_: *mut crate::leanh::LeanObject,
    mut v___y_6465_: *mut crate::leanh::LeanObject,
    mut v___y_6466_: *mut crate::leanh::LeanObject,
    mut v___y_6467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6468_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0(v_x_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_);
    crate::leanh::lean_dec(v___y_6466_);
    crate::leanh::lean_dec_ref(v___y_6465_);
    crate::leanh::lean_dec(v___y_6464_);
    crate::leanh::lean_dec_ref(v___y_6463_);
    crate::leanh::lean_dec_ref(v_x_6462_);
    return v_res_6468_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0(
    mut v_k_6469_: *mut crate::leanh::LeanObject,
    mut v_b_6470_: *mut crate::leanh::LeanObject,
    mut v___y_6471_: *mut crate::leanh::LeanObject,
    mut v___y_6472_: *mut crate::leanh::LeanObject,
    mut v___y_6473_: *mut crate::leanh::LeanObject,
    mut v___y_6474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_6474_);
    crate::leanh::lean_inc_ref(v___y_6473_);
    crate::leanh::lean_inc(v___y_6472_);
    crate::leanh::lean_inc_ref(v___y_6471_);
    v___x_6476_ = crate::leanh::lean_apply_6(
        v_k_6469_,
        v_b_6470_,
        v___y_6471_,
        v___y_6472_,
        v___y_6473_,
        v___y_6474_,
        crate::leanh::lean_box(0),
    );
    return v___x_6476_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_6477_: *mut crate::leanh::LeanObject,
    mut v_b_6478_: *mut crate::leanh::LeanObject,
    mut v___y_6479_: *mut crate::leanh::LeanObject,
    mut v___y_6480_: *mut crate::leanh::LeanObject,
    mut v___y_6481_: *mut crate::leanh::LeanObject,
    mut v___y_6482_: *mut crate::leanh::LeanObject,
    mut v___y_6483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6484_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0(v_k_6477_, v_b_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
    crate::leanh::lean_dec(v___y_6482_);
    crate::leanh::lean_dec_ref(v___y_6481_);
    crate::leanh::lean_dec(v___y_6480_);
    crate::leanh::lean_dec_ref(v___y_6479_);
    return v_res_6484_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(
    mut v_name_6485_: *mut crate::leanh::LeanObject,
    mut v_bi_6486_: u8,
    mut v_type_6487_: *mut crate::leanh::LeanObject,
    mut v_k_6488_: *mut crate::leanh::LeanObject,
    mut v_kind_6489_: u8,
    mut v___y_6490_: *mut crate::leanh::LeanObject,
    mut v___y_6491_: *mut crate::leanh::LeanObject,
    mut v___y_6492_: *mut crate::leanh::LeanObject,
    mut v___y_6493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6500_: u8 = 0;
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6504_: u8 = 0;
    let mut v_a_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6508_: u8 = 0;
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6495_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_6495_, 0, v_k_6488_);
                v___x_6496_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_6485_,
                    v_bi_6486_,
                    v_type_6487_,
                    v___f_6495_,
                    v_kind_6489_,
                    v___y_6490_,
                    v___y_6491_,
                    v___y_6492_,
                    v___y_6493_,
                );
                if crate::leanh::lean_obj_tag(v___x_6496_) == 0 {
                    v_a_6497_ = crate::leanh::lean_ctor_get(v___x_6496_, 0);
                    v_isSharedCheck_6504_ = (!crate::leanh::lean_is_exclusive(v___x_6496_)) as u8;
                    if v_isSharedCheck_6504_ == 0 {
                        v___x_6499_ = v___x_6496_;
                        v_isShared_6500_ = v_isSharedCheck_6504_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6497_);
                        crate::leanh::lean_dec(v___x_6496_);
                        v___x_6499_ = crate::leanh::lean_box(0);
                        v_isShared_6500_ = v_isSharedCheck_6504_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6505_ = crate::leanh::lean_ctor_get(v___x_6496_, 0);
                    v_isSharedCheck_6512_ = (!crate::leanh::lean_is_exclusive(v___x_6496_)) as u8;
                    if v_isSharedCheck_6512_ == 0 {
                        v___x_6507_ = v___x_6496_;
                        v_isShared_6508_ = v_isSharedCheck_6512_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6505_);
                        crate::leanh::lean_dec(v___x_6496_);
                        v___x_6507_ = crate::leanh::lean_box(0);
                        v_isShared_6508_ = v_isSharedCheck_6512_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6500_ == 0 {
                    v___x_6502_ = v___x_6499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6503_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6503_, 0, v_a_6497_);
                    v___x_6502_ = v_reuseFailAlloc_6503_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6502_;
            }
            3 => {
                if v_isShared_6508_ == 0 {
                    v___x_6510_ = v___x_6507_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6511_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6511_, 0, v_a_6505_);
                    v___x_6510_ = v_reuseFailAlloc_6511_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___boxed(
    mut v_name_6513_: *mut crate::leanh::LeanObject,
    mut v_bi_6514_: *mut crate::leanh::LeanObject,
    mut v_type_6515_: *mut crate::leanh::LeanObject,
    mut v_k_6516_: *mut crate::leanh::LeanObject,
    mut v_kind_6517_: *mut crate::leanh::LeanObject,
    mut v___y_6518_: *mut crate::leanh::LeanObject,
    mut v___y_6519_: *mut crate::leanh::LeanObject,
    mut v___y_6520_: *mut crate::leanh::LeanObject,
    mut v___y_6521_: *mut crate::leanh::LeanObject,
    mut v___y_6522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_6523_: u8 = 0;
    let mut v_kind_boxed_6524_: u8 = 0;
    let mut v_res_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_6523_ = (crate::leanh::lean_unbox(v_bi_6514_) as u8);
    v_kind_boxed_6524_ = (crate::leanh::lean_unbox(v_kind_6517_) as u8);
    v_res_6525_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_6513_, v_bi_boxed_6523_, v_type_6515_, v_k_6516_, v_kind_boxed_6524_, v___y_6518_, v___y_6519_, v___y_6520_, v___y_6521_);
    crate::leanh::lean_dec(v___y_6521_);
    crate::leanh::lean_dec_ref(v___y_6520_);
    crate::leanh::lean_dec(v___y_6519_);
    crate::leanh::lean_dec_ref(v___y_6518_);
    return v_res_6525_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(
    mut v_name_6526_: *mut crate::leanh::LeanObject,
    mut v_type_6527_: *mut crate::leanh::LeanObject,
    mut v_k_6528_: *mut crate::leanh::LeanObject,
    mut v___y_6529_: *mut crate::leanh::LeanObject,
    mut v___y_6530_: *mut crate::leanh::LeanObject,
    mut v___y_6531_: *mut crate::leanh::LeanObject,
    mut v___y_6532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6534_: u8 = 0;
    let mut v___x_6535_: u8 = 0;
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6534_ = 0;
    v___x_6535_ = 0;
    v___x_6536_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_6526_, v___x_6534_, v_type_6527_, v_k_6528_, v___x_6535_, v___y_6529_, v___y_6530_, v___y_6531_, v___y_6532_);
    return v___x_6536_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg___boxed(
    mut v_name_6537_: *mut crate::leanh::LeanObject,
    mut v_type_6538_: *mut crate::leanh::LeanObject,
    mut v_k_6539_: *mut crate::leanh::LeanObject,
    mut v___y_6540_: *mut crate::leanh::LeanObject,
    mut v___y_6541_: *mut crate::leanh::LeanObject,
    mut v___y_6542_: *mut crate::leanh::LeanObject,
    mut v___y_6543_: *mut crate::leanh::LeanObject,
    mut v___y_6544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6545_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v_name_6537_, v_type_6538_, v_k_6539_, v___y_6540_, v___y_6541_, v___y_6542_, v___y_6543_);
    crate::leanh::lean_dec(v___y_6543_);
    crate::leanh::lean_dec_ref(v___y_6542_);
    crate::leanh::lean_dec(v___y_6541_);
    crate::leanh::lean_dec_ref(v___y_6540_);
    return v_res_6545_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1(
    mut v___f_6549_: *mut crate::leanh::LeanObject,
    mut v_x_6550_: *mut crate::leanh::LeanObject,
    mut v_type_6551_: *mut crate::leanh::LeanObject,
    mut v___y_6552_: *mut crate::leanh::LeanObject,
    mut v___y_6553_: *mut crate::leanh::LeanObject,
    mut v___y_6554_: *mut crate::leanh::LeanObject,
    mut v___y_6555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6557_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__1;
    v___x_6558_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v___x_6557_, v_type_6551_, v___f_6549_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_);
    return v___x_6558_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___boxed(
    mut v___f_6559_: *mut crate::leanh::LeanObject,
    mut v_x_6560_: *mut crate::leanh::LeanObject,
    mut v_type_6561_: *mut crate::leanh::LeanObject,
    mut v___y_6562_: *mut crate::leanh::LeanObject,
    mut v___y_6563_: *mut crate::leanh::LeanObject,
    mut v___y_6564_: *mut crate::leanh::LeanObject,
    mut v___y_6565_: *mut crate::leanh::LeanObject,
    mut v___y_6566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6567_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1(v___f_6559_, v_x_6560_, v_type_6561_, v___y_6562_, v___y_6563_, v___y_6564_, v___y_6565_);
    crate::leanh::lean_dec(v___y_6565_);
    crate::leanh::lean_dec_ref(v___y_6564_);
    crate::leanh::lean_dec(v___y_6563_);
    crate::leanh::lean_dec_ref(v___y_6562_);
    crate::leanh::lean_dec_ref(v_x_6560_);
    return v_res_6567_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0(
    mut v___y_6574_: u8,
    mut v_suppressElabErrors_6575_: u8,
    mut v_x_6576_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_6576_) == 1 {
        let mut v_pre_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_6577_ = crate::leanh::lean_ctor_get(v_x_6576_, 0);
        match crate::leanh::lean_obj_tag(v_pre_6577_) {
            1 => {
                let mut v_pre_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_6578_ = crate::leanh::lean_ctor_get(v_pre_6577_, 0);
                match crate::leanh::lean_obj_tag(v_pre_6578_) {
                    0 => {
                        let mut v_str_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_6582_: u8 = 0;
                        v_str_6579_ = crate::leanh::lean_ctor_get(v_x_6576_, 1);
                        v_str_6580_ = crate::leanh::lean_ctor_get(v_pre_6577_, 1);
                        v___x_6581_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_;
                        v___x_6582_ = lean_string_dec_eq(v_str_6580_, v___x_6581_);
                        if v___x_6582_ == 0 {
                            let mut v___x_6583_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6584_: u8 = 0;
                            v___x_6583_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_;
                            v___x_6584_ = lean_string_dec_eq(v_str_6580_, v___x_6583_);
                            if v___x_6584_ == 0 {
                                return v___y_6574_;
                            } else {
                                let mut v___x_6585_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_6586_: u8 = 0;
                                v___x_6585_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__0;
                                v___x_6586_ = lean_string_dec_eq(v_str_6579_, v___x_6585_);
                                if v___x_6586_ == 0 {
                                    return v___y_6574_;
                                } else {
                                    return v_suppressElabErrors_6575_;
                                }
                            }
                        } else {
                            let mut v___x_6587_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6588_: u8 = 0;
                            v___x_6587_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__1;
                            v___x_6588_ = lean_string_dec_eq(v_str_6579_, v___x_6587_);
                            if v___x_6588_ == 0 {
                                return v___y_6574_;
                            } else {
                                return v_suppressElabErrors_6575_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_6589_ = crate::leanh::lean_ctor_get(v_pre_6578_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_6589_) == 0 {
                            let mut v_str_6590_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_6591_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_6592_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6593_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6594_: u8 = 0;
                            v_str_6590_ = crate::leanh::lean_ctor_get(v_x_6576_, 1);
                            v_str_6591_ = crate::leanh::lean_ctor_get(v_pre_6577_, 1);
                            v_str_6592_ = crate::leanh::lean_ctor_get(v_pre_6578_, 1);
                            v___x_6593_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__2;
                            v___x_6594_ = lean_string_dec_eq(v_str_6592_, v___x_6593_);
                            if v___x_6594_ == 0 {
                                return v___y_6574_;
                            } else {
                                let mut v___x_6595_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_6596_: u8 = 0;
                                v___x_6595_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__3;
                                v___x_6596_ = lean_string_dec_eq(v_str_6591_, v___x_6595_);
                                if v___x_6596_ == 0 {
                                    return v___y_6574_;
                                } else {
                                    let mut v___x_6597_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_6598_: u8 = 0;
                                    v___x_6597_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__4;
                                    v___x_6598_ = lean_string_dec_eq(v_str_6590_, v___x_6597_);
                                    if v___x_6598_ == 0 {
                                        return v___y_6574_;
                                    } else {
                                        return v_suppressElabErrors_6575_;
                                    }
                                }
                            }
                        } else {
                            return v___y_6574_;
                        }
                    }
                    _ => {
                        return v___y_6574_;
                    }
                }
            }
            0 => {
                let mut v_str_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6601_: u8 = 0;
                v_str_6599_ = crate::leanh::lean_ctor_get(v_x_6576_, 1);
                v___x_6600_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5;
                v___x_6601_ = lean_string_dec_eq(v_str_6599_, v___x_6600_);
                if v___x_6601_ == 0 {
                    return v___y_6574_;
                } else {
                    return v_suppressElabErrors_6575_;
                }
            }
            _ => {
                return v___y_6574_;
            }
        }
    } else {
        return v___y_6574_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed(
    mut v___y_6602_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_6603_: *mut crate::leanh::LeanObject,
    mut v_x_6604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5356__boxed_6605_: u8 = 0;
    let mut v_suppressElabErrors_boxed_6606_: u8 = 0;
    let mut v_res_6607_: u8 = 0;
    let mut v_r_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_5356__boxed_6605_ = (crate::leanh::lean_unbox(v___y_6602_) as u8);
    v_suppressElabErrors_boxed_6606_ = (crate::leanh::lean_unbox(v_suppressElabErrors_6603_) as u8);
    v_res_6607_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0(v___y_5356__boxed_6605_, v_suppressElabErrors_boxed_6606_, v_x_6604_);
    crate::leanh::lean_dec(v_x_6604_);
    v_r_6608_ = crate::leanh::lean_box((v_res_6607_) as usize);
    return v_r_6608_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(
    mut v_ref_6609_: *mut crate::leanh::LeanObject,
    mut v_msgData_6610_: *mut crate::leanh::LeanObject,
    mut v_severity_6611_: u8,
    mut v_isSilent_6612_: u8,
    mut v___y_6613_: *mut crate::leanh::LeanObject,
    mut v___y_6614_: *mut crate::leanh::LeanObject,
    mut v___y_6615_: *mut crate::leanh::LeanObject,
    mut v___y_6616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6620_: u8 = 0;
    let mut v___y_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6624_: u8 = 0;
    let mut v___y_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6642_: u8 = 0;
    let mut v___x_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6653_: u8 = 0;
    let mut v___y_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6658_: u8 = 0;
    let mut v___y_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6660_: u8 = 0;
    let mut v___y_6661_: u8 = 0;
    let mut v___y_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6668_: u8 = 0;
    let mut v___x_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: u8 = 0;
    let mut v___x_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6678_: u8 = 0;
    let mut v___y_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6682_: u8 = 0;
    let mut v___y_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6684_: u8 = 0;
    let mut v___y_6685_: u8 = 0;
    let mut v___y_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6695_: u8 = 0;
    let mut v___y_6696_: u8 = 0;
    let mut v___y_6697_: u8 = 0;
    let mut v_ref_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: u8 = 0;
    let mut v___y_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6708_: u8 = 0;
    let mut v___y_6709_: u8 = 0;
    let mut v___y_6710_: u8 = 0;
    let mut v___y_6712_: u8 = 0;
    let mut v_fileName_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6717_: u8 = 0;
    let mut v___x_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: u8 = 0;
    let mut v___x_6722_: u8 = 0;
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: u8 = 0;
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: u8 = 0;
    let mut v___x_6728_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6702_ = 2;
                v___x_6727_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6611_, v___x_6702_);
                if v___x_6727_ == 0 {
                    v___y_6712_ = v___x_6727_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_6610_);
                    v___x_6728_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6610_);
                    v___y_6712_ = v___x_6728_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_6628_ = lean_st_ref_take(v___y_6627_);
                v_currNamespace_6629_ = crate::leanh::lean_ctor_get(v___y_6626_, 6);
                v_openDecls_6630_ = crate::leanh::lean_ctor_get(v___y_6626_, 7);
                v_env_6631_ = crate::leanh::lean_ctor_get(v___x_6628_, 0);
                v_nextMacroScope_6632_ = crate::leanh::lean_ctor_get(v___x_6628_, 1);
                v_ngen_6633_ = crate::leanh::lean_ctor_get(v___x_6628_, 2);
                v_auxDeclNGen_6634_ = crate::leanh::lean_ctor_get(v___x_6628_, 3);
                v_traceState_6635_ = crate::leanh::lean_ctor_get(v___x_6628_, 4);
                v_cache_6636_ = crate::leanh::lean_ctor_get(v___x_6628_, 5);
                v_messages_6637_ = crate::leanh::lean_ctor_get(v___x_6628_, 6);
                v_infoState_6638_ = crate::leanh::lean_ctor_get(v___x_6628_, 7);
                v_snapshotTasks_6639_ = crate::leanh::lean_ctor_get(v___x_6628_, 8);
                v_isSharedCheck_6653_ = (!crate::leanh::lean_is_exclusive(v___x_6628_)) as u8;
                if v_isSharedCheck_6653_ == 0 {
                    v___x_6641_ = v___x_6628_;
                    v_isShared_6642_ = v_isSharedCheck_6653_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6639_);
                    crate::leanh::lean_inc(v_infoState_6638_);
                    crate::leanh::lean_inc(v_messages_6637_);
                    crate::leanh::lean_inc(v_cache_6636_);
                    crate::leanh::lean_inc(v_traceState_6635_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6634_);
                    crate::leanh::lean_inc(v_ngen_6633_);
                    crate::leanh::lean_inc(v_nextMacroScope_6632_);
                    crate::leanh::lean_inc(v_env_6631_);
                    crate::leanh::lean_dec(v___x_6628_);
                    v___x_6641_ = crate::leanh::lean_box(0);
                    v_isShared_6642_ = v_isSharedCheck_6653_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_6630_);
                crate::leanh::lean_inc(v_currNamespace_6629_);
                v___x_6643_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6643_, 0, v_currNamespace_6629_);
                crate::leanh::lean_ctor_set(v___x_6643_, 1, v_openDecls_6630_);
                v___x_6644_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6644_, 0, v___x_6643_);
                crate::leanh::lean_ctor_set(v___x_6644_, 1, v___y_6621_);
                crate::leanh::lean_inc_ref(v___y_6623_);
                crate::leanh::lean_inc_ref(v___y_6619_);
                v___x_6645_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_6645_, 0, v___y_6619_);
                crate::leanh::lean_ctor_set(v___x_6645_, 1, v___y_6622_);
                crate::leanh::lean_ctor_set(v___x_6645_, 2, v___y_6625_);
                crate::leanh::lean_ctor_set(v___x_6645_, 3, v___y_6623_);
                crate::leanh::lean_ctor_set(v___x_6645_, 4, v___x_6644_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_6624_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_6620_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_6612_,
                );
                v___x_6646_ = l_Lean_MessageLog_add(v___x_6645_, v_messages_6637_);
                if v_isShared_6642_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6641_, 6, v___x_6646_);
                    v___x_6648_ = v___x_6641_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6652_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 0, v_env_6631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 1, v_nextMacroScope_6632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 2, v_ngen_6633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 3, v_auxDeclNGen_6634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 4, v_traceState_6635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 5, v_cache_6636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 6, v___x_6646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 7, v_infoState_6638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 8, v_snapshotTasks_6639_);
                    v___x_6648_ = v_reuseFailAlloc_6652_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6649_ = lean_st_ref_set(v___y_6627_, v___x_6648_);
                v___x_6650_ = crate::leanh::lean_box(0);
                v___x_6651_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6651_, 0, v___x_6650_);
                return v___x_6651_;
            }
            4 => {
                v___x_6663_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_6610_,
                    );
                v___x_6664_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v___x_6663_, v___y_6613_, v___y_6614_, v___y_6615_, v___y_6616_);
                v_a_6665_ = crate::leanh::lean_ctor_get(v___x_6664_, 0);
                v_isSharedCheck_6678_ = (!crate::leanh::lean_is_exclusive(v___x_6664_)) as u8;
                if v_isSharedCheck_6678_ == 0 {
                    v___x_6667_ = v___x_6664_;
                    v_isShared_6668_ = v_isSharedCheck_6678_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6665_);
                    crate::leanh::lean_dec(v___x_6664_);
                    v___x_6667_ = crate::leanh::lean_box(0);
                    v_isShared_6668_ = v_isSharedCheck_6678_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_6659_, 2);
                v___x_6669_ = l_Lean_FileMap_toPosition(v___y_6659_, v___y_6656_);
                crate::leanh::lean_dec(v___y_6656_);
                v___x_6670_ = l_Lean_FileMap_toPosition(v___y_6659_, v___y_6662_);
                crate::leanh::lean_dec(v___y_6662_);
                v___x_6671_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6671_, 0, v___x_6670_);
                v___x_6672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3;
                if v___y_6661_ == 0 {
                    crate::leanh::lean_del_object(v___x_6667_);
                    crate::leanh::lean_dec_ref(v___y_6655_);
                    v___y_6619_ = v___y_6657_;
                    v___y_6620_ = v___y_6658_;
                    v___y_6621_ = v_a_6665_;
                    v___y_6622_ = v___x_6669_;
                    v___y_6623_ = v___x_6672_;
                    v___y_6624_ = v___y_6660_;
                    v___y_6625_ = v___x_6671_;
                    v___y_6626_ = v___y_6615_;
                    v___y_6627_ = v___y_6616_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6665_);
                    v___x_6673_ = l_Lean_MessageData_hasTag(v___y_6655_, v_a_6665_);
                    if v___x_6673_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6671_, 1);
                        crate::leanh::lean_dec_ref(v___x_6669_);
                        crate::leanh::lean_dec(v_a_6665_);
                        v___x_6674_ = crate::leanh::lean_box(0);
                        if v_isShared_6668_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6667_, 0, v___x_6674_);
                            v___x_6676_ = v___x_6667_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_6677_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6677_, 0, v___x_6674_);
                            v___x_6676_ = v_reuseFailAlloc_6677_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6667_);
                        v___y_6619_ = v___y_6657_;
                        v___y_6620_ = v___y_6658_;
                        v___y_6621_ = v_a_6665_;
                        v___y_6622_ = v___x_6669_;
                        v___y_6623_ = v___x_6672_;
                        v___y_6624_ = v___y_6660_;
                        v___y_6625_ = v___x_6671_;
                        v___y_6626_ = v___y_6615_;
                        v___y_6627_ = v___y_6616_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_6676_;
            }
            7 => {
                v___x_6688_ = l_Lean_Syntax_getTailPos_x3f(v___y_6686_, v___y_6684_);
                crate::leanh::lean_dec(v___y_6686_);
                if crate::leanh::lean_obj_tag(v___x_6688_) == 0 {
                    crate::leanh::lean_inc(v___y_6687_);
                    v___y_6655_ = v___y_6680_;
                    v___y_6656_ = v___y_6687_;
                    v___y_6657_ = v___y_6681_;
                    v___y_6658_ = v___y_6682_;
                    v___y_6659_ = v___y_6683_;
                    v___y_6660_ = v___y_6684_;
                    v___y_6661_ = v___y_6685_;
                    v___y_6662_ = v___y_6687_;
                    state = 4;
                    continue;
                } else {
                    v_val_6689_ = crate::leanh::lean_ctor_get(v___x_6688_, 0);
                    crate::leanh::lean_inc(v_val_6689_);
                    crate::leanh::lean_dec_ref_known(v___x_6688_, 1);
                    v___y_6655_ = v___y_6680_;
                    v___y_6656_ = v___y_6687_;
                    v___y_6657_ = v___y_6681_;
                    v___y_6658_ = v___y_6682_;
                    v___y_6659_ = v___y_6683_;
                    v___y_6660_ = v___y_6684_;
                    v___y_6661_ = v___y_6685_;
                    v___y_6662_ = v_val_6689_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_6698_ = l_Lean_replaceRef(v_ref_6609_, v___y_6693_);
                v___x_6699_ = l_Lean_Syntax_getPos_x3f(v_ref_6698_, v___y_6695_);
                if crate::leanh::lean_obj_tag(v___x_6699_) == 0 {
                    v___x_6700_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6680_ = v___y_6691_;
                    v___y_6681_ = v___y_6692_;
                    v___y_6682_ = v___y_6697_;
                    v___y_6683_ = v___y_6694_;
                    v___y_6684_ = v___y_6695_;
                    v___y_6685_ = v___y_6696_;
                    v___y_6686_ = v_ref_6698_;
                    v___y_6687_ = v___x_6700_;
                    state = 7;
                    continue;
                } else {
                    v_val_6701_ = crate::leanh::lean_ctor_get(v___x_6699_, 0);
                    crate::leanh::lean_inc(v_val_6701_);
                    crate::leanh::lean_dec_ref_known(v___x_6699_, 1);
                    v___y_6680_ = v___y_6691_;
                    v___y_6681_ = v___y_6692_;
                    v___y_6682_ = v___y_6697_;
                    v___y_6683_ = v___y_6694_;
                    v___y_6684_ = v___y_6695_;
                    v___y_6685_ = v___y_6696_;
                    v___y_6686_ = v_ref_6698_;
                    v___y_6687_ = v_val_6701_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_6710_ == 0 {
                    v___y_6691_ = v___y_6707_;
                    v___y_6692_ = v___y_6704_;
                    v___y_6693_ = v___y_6705_;
                    v___y_6694_ = v___y_6706_;
                    v___y_6695_ = v___y_6709_;
                    v___y_6696_ = v___y_6708_;
                    v___y_6697_ = v_severity_6611_;
                    state = 8;
                    continue;
                } else {
                    v___y_6691_ = v___y_6707_;
                    v___y_6692_ = v___y_6704_;
                    v___y_6693_ = v___y_6705_;
                    v___y_6694_ = v___y_6706_;
                    v___y_6695_ = v___y_6709_;
                    v___y_6696_ = v___y_6708_;
                    v___y_6697_ = v___x_6702_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_6712_ == 0 {
                    v_fileName_6713_ = crate::leanh::lean_ctor_get(v___y_6615_, 0);
                    v_fileMap_6714_ = crate::leanh::lean_ctor_get(v___y_6615_, 1);
                    v_options_6715_ = crate::leanh::lean_ctor_get(v___y_6615_, 2);
                    v_ref_6716_ = crate::leanh::lean_ctor_get(v___y_6615_, 5);
                    v_suppressElabErrors_6717_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_6615_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_6718_ = crate::leanh::lean_box((v___y_6712_) as usize);
                    v___x_6719_ = crate::leanh::lean_box((v_suppressElabErrors_6717_) as usize);
                    v___f_6720_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_6720_, 0, v___x_6718_);
                    crate::leanh::lean_closure_set(v___f_6720_, 1, v___x_6719_);
                    v___x_6721_ = 1;
                    v___x_6722_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6611_, v___x_6721_);
                    if v___x_6722_ == 0 {
                        v___y_6704_ = v_fileName_6713_;
                        v___y_6705_ = v_ref_6716_;
                        v___y_6706_ = v_fileMap_6714_;
                        v___y_6707_ = v___f_6720_;
                        v___y_6708_ = v_suppressElabErrors_6717_;
                        v___y_6709_ = v___y_6712_;
                        v___y_6710_ = v___x_6722_;
                        state = 9;
                        continue;
                    } else {
                        v___x_6723_ = l_Lean_warningAsError;
                        v___x_6724_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(v_options_6715_, v___x_6723_);
                        v___y_6704_ = v_fileName_6713_;
                        v___y_6705_ = v_ref_6716_;
                        v___y_6706_ = v_fileMap_6714_;
                        v___y_6707_ = v___f_6720_;
                        v___y_6708_ = v_suppressElabErrors_6717_;
                        v___y_6709_ = v___y_6712_;
                        v___y_6710_ = v___x_6724_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_6610_);
                    v___x_6725_ = crate::leanh::lean_box(0);
                    v___x_6726_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6726_, 0, v___x_6725_);
                    return v___x_6726_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___boxed(
    mut v_ref_6729_: *mut crate::leanh::LeanObject,
    mut v_msgData_6730_: *mut crate::leanh::LeanObject,
    mut v_severity_6731_: *mut crate::leanh::LeanObject,
    mut v_isSilent_6732_: *mut crate::leanh::LeanObject,
    mut v___y_6733_: *mut crate::leanh::LeanObject,
    mut v___y_6734_: *mut crate::leanh::LeanObject,
    mut v___y_6735_: *mut crate::leanh::LeanObject,
    mut v___y_6736_: *mut crate::leanh::LeanObject,
    mut v___y_6737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_6738_: u8 = 0;
    let mut v_isSilent_boxed_6739_: u8 = 0;
    let mut v_res_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6738_ = (crate::leanh::lean_unbox(v_severity_6731_) as u8);
    v_isSilent_boxed_6739_ = (crate::leanh::lean_unbox(v_isSilent_6732_) as u8);
    v_res_6740_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(v_ref_6729_, v_msgData_6730_, v_severity_boxed_6738_, v_isSilent_boxed_6739_, v___y_6733_, v___y_6734_, v___y_6735_, v___y_6736_);
    crate::leanh::lean_dec(v___y_6736_);
    crate::leanh::lean_dec_ref(v___y_6735_);
    crate::leanh::lean_dec(v___y_6734_);
    crate::leanh::lean_dec_ref(v___y_6733_);
    crate::leanh::lean_dec(v_ref_6729_);
    return v_res_6740_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(
    mut v_msgData_6741_: *mut crate::leanh::LeanObject,
    mut v_severity_6742_: u8,
    mut v_isSilent_6743_: u8,
    mut v___y_6744_: *mut crate::leanh::LeanObject,
    mut v___y_6745_: *mut crate::leanh::LeanObject,
    mut v___y_6746_: *mut crate::leanh::LeanObject,
    mut v___y_6747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_6749_ = crate::leanh::lean_ctor_get(v___y_6746_, 5);
    v___x_6750_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(v_ref_6749_, v_msgData_6741_, v_severity_6742_, v_isSilent_6743_, v___y_6744_, v___y_6745_, v___y_6746_, v___y_6747_);
    return v___x_6750_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4___boxed(
    mut v_msgData_6751_: *mut crate::leanh::LeanObject,
    mut v_severity_6752_: *mut crate::leanh::LeanObject,
    mut v_isSilent_6753_: *mut crate::leanh::LeanObject,
    mut v___y_6754_: *mut crate::leanh::LeanObject,
    mut v___y_6755_: *mut crate::leanh::LeanObject,
    mut v___y_6756_: *mut crate::leanh::LeanObject,
    mut v___y_6757_: *mut crate::leanh::LeanObject,
    mut v___y_6758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_6759_: u8 = 0;
    let mut v_isSilent_boxed_6760_: u8 = 0;
    let mut v_res_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6759_ = (crate::leanh::lean_unbox(v_severity_6752_) as u8);
    v_isSilent_boxed_6760_ = (crate::leanh::lean_unbox(v_isSilent_6753_) as u8);
    v_res_6761_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(v_msgData_6751_, v_severity_boxed_6759_, v_isSilent_boxed_6760_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_);
    crate::leanh::lean_dec(v___y_6757_);
    crate::leanh::lean_dec_ref(v___y_6756_);
    crate::leanh::lean_dec(v___y_6755_);
    crate::leanh::lean_dec_ref(v___y_6754_);
    return v_res_6761_;
}
pub unsafe fn l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(
    mut v_msgData_6762_: *mut crate::leanh::LeanObject,
    mut v___y_6763_: *mut crate::leanh::LeanObject,
    mut v___y_6764_: *mut crate::leanh::LeanObject,
    mut v___y_6765_: *mut crate::leanh::LeanObject,
    mut v___y_6766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6768_: u8 = 0;
    let mut v___x_6769_: u8 = 0;
    let mut v___x_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6768_ = 0;
    v___x_6769_ = 0;
    v___x_6770_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(v_msgData_6762_, v___x_6768_, v___x_6769_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_);
    return v___x_6770_;
}
pub unsafe fn l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3___boxed(
    mut v_msgData_6771_: *mut crate::leanh::LeanObject,
    mut v___y_6772_: *mut crate::leanh::LeanObject,
    mut v___y_6773_: *mut crate::leanh::LeanObject,
    mut v___y_6774_: *mut crate::leanh::LeanObject,
    mut v___y_6775_: *mut crate::leanh::LeanObject,
    mut v___y_6776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6777_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v_msgData_6771_, v___y_6772_, v___y_6773_, v___y_6774_, v___y_6775_);
    crate::leanh::lean_dec(v___y_6775_);
    crate::leanh::lean_dec_ref(v___y_6774_);
    crate::leanh::lean_dec(v___y_6773_);
    crate::leanh::lean_dec_ref(v___y_6772_);
    return v_res_6777_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(
    mut v_constName_6778_: *mut crate::leanh::LeanObject,
    mut v___y_6779_: *mut crate::leanh::LeanObject,
    mut v___y_6780_: *mut crate::leanh::LeanObject,
    mut v___y_6781_: *mut crate::leanh::LeanObject,
    mut v___y_6782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: u8 = 0;
    let mut v___x_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6792_: u8 = 0;
    let mut v___x_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6784_ = lean_st_ref_get(v___y_6782_);
                v_env_6785_ = crate::leanh::lean_ctor_get(v___x_6784_, 0);
                crate::leanh::lean_inc_ref(v_env_6785_);
                crate::leanh::lean_dec(v___x_6784_);
                v___x_6786_ = 0;
                crate::leanh::lean_inc(v_constName_6778_);
                v___x_6787_ =
                    l_Lean_Environment_find_x3f(v_env_6785_, v_constName_6778_, v___x_6786_);
                if crate::leanh::lean_obj_tag(v___x_6787_) == 0 {
                    v___x_6788_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_6778_, v___y_6779_, v___y_6780_, v___y_6781_, v___y_6782_);
                    return v___x_6788_;
                } else {
                    crate::leanh::lean_dec(v_constName_6778_);
                    v_val_6789_ = crate::leanh::lean_ctor_get(v___x_6787_, 0);
                    v_isSharedCheck_6796_ = (!crate::leanh::lean_is_exclusive(v___x_6787_)) as u8;
                    if v_isSharedCheck_6796_ == 0 {
                        v___x_6791_ = v___x_6787_;
                        v_isShared_6792_ = v_isSharedCheck_6796_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6789_);
                        crate::leanh::lean_dec(v___x_6787_);
                        v___x_6791_ = crate::leanh::lean_box(0);
                        v_isShared_6792_ = v_isSharedCheck_6796_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6792_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6791_, 0);
                    v___x_6794_ = v___x_6791_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6795_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6795_, 0, v_val_6789_);
                    v___x_6794_ = v_reuseFailAlloc_6795_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1___boxed(
    mut v_constName_6797_: *mut crate::leanh::LeanObject,
    mut v___y_6798_: *mut crate::leanh::LeanObject,
    mut v___y_6799_: *mut crate::leanh::LeanObject,
    mut v___y_6800_: *mut crate::leanh::LeanObject,
    mut v___y_6801_: *mut crate::leanh::LeanObject,
    mut v___y_6802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6803_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(v_constName_6797_, v___y_6798_, v___y_6799_, v___y_6800_, v___y_6801_);
    crate::leanh::lean_dec(v___y_6801_);
    crate::leanh::lean_dec_ref(v___y_6800_);
    crate::leanh::lean_dec(v___y_6799_);
    crate::leanh::lean_dec_ref(v___y_6798_);
    return v_res_6803_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6808_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2;
    v___x_6809_ = l_Lean_stringToMessageData(v___x_6808_);
    return v___x_6809_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6811_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__4;
    v___x_6812_ = l_Lean_stringToMessageData(v___x_6811_);
    return v___x_6812_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6814_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__6;
    v___x_6815_ = l_Lean_stringToMessageData(v___x_6814_);
    return v___x_6815_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6817_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__8;
    v___x_6818_ = l_Lean_stringToMessageData(v___x_6817_);
    return v___x_6818_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6820_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__10;
    v___x_6821_ = l_Lean_stringToMessageData(v___x_6820_);
    return v___x_6821_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(
    mut v_declName_6822_: *mut crate::leanh::LeanObject,
    mut v_params_6823_: *mut crate::leanh::LeanObject,
    mut v_a_6824_: *mut crate::leanh::LeanObject,
    mut v_a_6825_: *mut crate::leanh::LeanObject,
    mut v_a_6826_: *mut crate::leanh::LeanObject,
    mut v_a_6827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: u8 = 0;
    let mut v___x_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6840_: u8 = 0;
    let mut v_counters_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thm_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instances_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_min_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_detailed_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: u8 = 0;
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: u8 = 0;
    let mut v___x_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6870_: u8 = 0;
    let mut v___x_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6874_: u8 = 0;
    let mut v_a_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6878_: u8 = 0;
    let mut v___x_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6882_: u8 = 0;
    let mut v___x_6883_: u8 = 0;
    let mut v___x_6884_: u8 = 0;
    let mut v___x_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6900_: u8 = 0;
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6904_: u8 = 0;
    let mut v___x_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6920_: u8 = 0;
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6924_: u8 = 0;
    let mut v_isSharedCheck_6925_: u8 = 0;
    let mut v_a_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6929_: u8 = 0;
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6933_: u8 = 0;
    let mut v_a_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6937_: u8 = 0;
    let mut v___x_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6941_: u8 = 0;
    let mut v_a_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6945_: u8 = 0;
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_6822_);
                v___x_6829_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(v_declName_6822_, v_a_6824_, v_a_6825_, v_a_6826_, v_a_6827_);
                if crate::leanh::lean_obj_tag(v___x_6829_) == 0 {
                    v_a_6830_ = crate::leanh::lean_ctor_get(v___x_6829_, 0);
                    crate::leanh::lean_inc(v_a_6830_);
                    crate::leanh::lean_dec_ref_known(v___x_6829_, 1);
                    v___f_6831_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__1;
                    v___x_6832_ = l_Lean_ConstantInfo_type(v_a_6830_);
                    crate::leanh::lean_dec(v_a_6830_);
                    v___x_6833_ = 0;
                    v___x_6834_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v___x_6832_, v___f_6831_, v___x_6833_, v_a_6824_, v_a_6825_, v_a_6826_, v_a_6827_);
                    if crate::leanh::lean_obj_tag(v___x_6834_) == 0 {
                        v_a_6835_ = crate::leanh::lean_ctor_get(v___x_6834_, 0);
                        crate::leanh::lean_inc(v_a_6835_);
                        crate::leanh::lean_dec_ref_known(v___x_6834_, 1);
                        crate::leanh::lean_inc_ref(v_params_6823_);
                        v___x_6836_ = l_Lean_Meta_Grind_main(
                            v_a_6835_,
                            v_params_6823_,
                            v_a_6824_,
                            v_a_6825_,
                            v_a_6826_,
                            v_a_6827_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6836_) == 0 {
                            v_a_6837_ = crate::leanh::lean_ctor_get(v___x_6836_, 0);
                            v_isSharedCheck_6925_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6836_)) as u8;
                            if v_isSharedCheck_6925_ == 0 {
                                v___x_6839_ = v___x_6836_;
                                v_isShared_6840_ = v_isSharedCheck_6925_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6837_);
                                crate::leanh::lean_dec(v___x_6836_);
                                v___x_6839_ = crate::leanh::lean_box(0);
                                v_isShared_6840_ = v_isSharedCheck_6925_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_params_6823_);
                            crate::leanh::lean_dec(v_declName_6822_);
                            v_a_6926_ = crate::leanh::lean_ctor_get(v___x_6836_, 0);
                            v_isSharedCheck_6933_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6836_)) as u8;
                            if v_isSharedCheck_6933_ == 0 {
                                v___x_6928_ = v___x_6836_;
                                v_isShared_6929_ = v_isSharedCheck_6933_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6926_);
                                crate::leanh::lean_dec(v___x_6836_);
                                v___x_6928_ = crate::leanh::lean_box(0);
                                v_isShared_6929_ = v_isSharedCheck_6933_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_params_6823_);
                        crate::leanh::lean_dec(v_declName_6822_);
                        v_a_6934_ = crate::leanh::lean_ctor_get(v___x_6834_, 0);
                        v_isSharedCheck_6941_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6834_)) as u8;
                        if v_isSharedCheck_6941_ == 0 {
                            v___x_6936_ = v___x_6834_;
                            v_isShared_6937_ = v_isSharedCheck_6941_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6934_);
                            crate::leanh::lean_dec(v___x_6834_);
                            v___x_6936_ = crate::leanh::lean_box(0);
                            v_isShared_6937_ = v_isSharedCheck_6941_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_params_6823_);
                    crate::leanh::lean_dec(v_declName_6822_);
                    v_a_6942_ = crate::leanh::lean_ctor_get(v___x_6829_, 0);
                    v_isSharedCheck_6949_ = (!crate::leanh::lean_is_exclusive(v___x_6829_)) as u8;
                    if v_isSharedCheck_6949_ == 0 {
                        v___x_6944_ = v___x_6829_;
                        v_isShared_6945_ = v_isSharedCheck_6949_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6942_);
                        crate::leanh::lean_dec(v___x_6829_);
                        v___x_6944_ = crate::leanh::lean_box(0);
                        v_isShared_6945_ = v_isSharedCheck_6949_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v_counters_6841_ = crate::leanh::lean_ctor_get(v_a_6837_, 3);
                crate::leanh::lean_inc_ref(v_counters_6841_);
                crate::leanh::lean_dec(v_a_6837_);
                v_config_6842_ = crate::leanh::lean_ctor_get(v_params_6823_, 0);
                crate::leanh::lean_inc_ref(v_config_6842_);
                crate::leanh::lean_dec_ref(v_params_6823_);
                v_thm_6843_ = crate::leanh::lean_ctor_get(v_counters_6841_, 0);
                crate::leanh::lean_inc_ref(v_thm_6843_);
                crate::leanh::lean_dec_ref(v_counters_6841_);
                v_instances_6844_ = crate::leanh::lean_ctor_get(v_config_6842_, 4);
                crate::leanh::lean_inc(v_instances_6844_);
                v_min_6845_ = crate::leanh::lean_ctor_get(v_config_6842_, 10);
                crate::leanh::lean_inc(v_min_6845_);
                v_detailed_6846_ = crate::leanh::lean_ctor_get(v_config_6842_, 11);
                crate::leanh::lean_inc(v_detailed_6846_);
                crate::leanh::lean_dec_ref(v_config_6842_);
                v___x_6847_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(
                    v_thm_6843_,
                );
                v___x_6883_ = lean_nat_dec_lt(v_min_6845_, v___x_6847_);
                if v___x_6883_ == 0 {
                    crate::leanh::lean_dec(v_instances_6844_);
                    v___y_6855_ = v_a_6824_;
                    v___y_6856_ = v_a_6825_;
                    v___y_6857_ = v_a_6826_;
                    v___y_6858_ = v_a_6827_;
                    state = 4;
                    continue;
                } else {
                    v___x_6884_ = lean_nat_dec_le(v_instances_6844_, v___x_6847_);
                    crate::leanh::lean_dec(v_instances_6844_);
                    if v___x_6884_ == 0 {
                        v___x_6885_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5);
                        crate::leanh::lean_inc(v_declName_6822_);
                        v___x_6886_ = l_Lean_MessageData_ofName(v_declName_6822_);
                        v___x_6887_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6887_, 0, v___x_6885_);
                        crate::leanh::lean_ctor_set(v___x_6887_, 1, v___x_6886_);
                        v___x_6888_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7);
                        v___x_6889_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6889_, 0, v___x_6887_);
                        crate::leanh::lean_ctor_set(v___x_6889_, 1, v___x_6888_);
                        crate::leanh::lean_inc(v___x_6847_);
                        v___x_6890_ = l_Nat_reprFast(v___x_6847_);
                        v___x_6891_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6891_, 0, v___x_6890_);
                        v___x_6892_ = l_Lean_MessageData_ofFormat(v___x_6891_);
                        v___x_6893_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6893_, 0, v___x_6889_);
                        crate::leanh::lean_ctor_set(v___x_6893_, 1, v___x_6892_);
                        v___x_6894_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9);
                        v___x_6895_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6895_, 0, v___x_6893_);
                        crate::leanh::lean_ctor_set(v___x_6895_, 1, v___x_6894_);
                        v___x_6896_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_6895_, v_a_6824_, v_a_6825_, v_a_6826_, v_a_6827_);
                        if crate::leanh::lean_obj_tag(v___x_6896_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6896_, 1);
                            v___y_6855_ = v_a_6824_;
                            v___y_6856_ = v_a_6825_;
                            v___y_6857_ = v_a_6826_;
                            v___y_6858_ = v_a_6827_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6847_);
                            crate::leanh::lean_dec(v_detailed_6846_);
                            crate::leanh::lean_dec(v_min_6845_);
                            crate::leanh::lean_dec_ref(v_thm_6843_);
                            crate::leanh::lean_del_object(v___x_6839_);
                            crate::leanh::lean_dec(v_declName_6822_);
                            v_a_6897_ = crate::leanh::lean_ctor_get(v___x_6896_, 0);
                            v_isSharedCheck_6904_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6896_)) as u8;
                            if v_isSharedCheck_6904_ == 0 {
                                v___x_6899_ = v___x_6896_;
                                v_isShared_6900_ = v_isSharedCheck_6904_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6897_);
                                crate::leanh::lean_dec(v___x_6896_);
                                v___x_6899_ = crate::leanh::lean_box(0);
                                v_isShared_6900_ = v_isSharedCheck_6904_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        v___x_6905_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5);
                        crate::leanh::lean_inc(v_declName_6822_);
                        v___x_6906_ = l_Lean_MessageData_ofName(v_declName_6822_);
                        v___x_6907_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6907_, 0, v___x_6905_);
                        crate::leanh::lean_ctor_set(v___x_6907_, 1, v___x_6906_);
                        v___x_6908_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11);
                        v___x_6909_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6909_, 0, v___x_6907_);
                        crate::leanh::lean_ctor_set(v___x_6909_, 1, v___x_6908_);
                        crate::leanh::lean_inc(v___x_6847_);
                        v___x_6910_ = l_Nat_reprFast(v___x_6847_);
                        v___x_6911_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6911_, 0, v___x_6910_);
                        v___x_6912_ = l_Lean_MessageData_ofFormat(v___x_6911_);
                        v___x_6913_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6913_, 0, v___x_6909_);
                        crate::leanh::lean_ctor_set(v___x_6913_, 1, v___x_6912_);
                        v___x_6914_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9);
                        v___x_6915_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6915_, 0, v___x_6913_);
                        crate::leanh::lean_ctor_set(v___x_6915_, 1, v___x_6914_);
                        v___x_6916_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_6915_, v_a_6824_, v_a_6825_, v_a_6826_, v_a_6827_);
                        if crate::leanh::lean_obj_tag(v___x_6916_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6916_, 1);
                            v___y_6855_ = v_a_6824_;
                            v___y_6856_ = v_a_6825_;
                            v___y_6857_ = v_a_6826_;
                            v___y_6858_ = v_a_6827_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6847_);
                            crate::leanh::lean_dec(v_detailed_6846_);
                            crate::leanh::lean_dec(v_min_6845_);
                            crate::leanh::lean_dec_ref(v_thm_6843_);
                            crate::leanh::lean_del_object(v___x_6839_);
                            crate::leanh::lean_dec(v_declName_6822_);
                            v_a_6917_ = crate::leanh::lean_ctor_get(v___x_6916_, 0);
                            v_isSharedCheck_6924_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6916_)) as u8;
                            if v_isSharedCheck_6924_ == 0 {
                                v___x_6919_ = v___x_6916_;
                                v_isShared_6920_ = v_isSharedCheck_6924_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6917_);
                                crate::leanh::lean_dec(v___x_6916_);
                                v___x_6919_ = crate::leanh::lean_box(0);
                                v_isShared_6920_ = v_isSharedCheck_6924_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_6849_ = lean_nat_dec_lt(v_min_6845_, v___x_6847_);
                crate::leanh::lean_dec(v___x_6847_);
                crate::leanh::lean_dec(v_min_6845_);
                v___x_6850_ = crate::leanh::lean_box((v___x_6849_) as usize);
                if v_isShared_6840_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6839_, 0, v___x_6850_);
                    v___x_6852_ = v___x_6839_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6853_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6853_, 0, v___x_6850_);
                    v___x_6852_ = v_reuseFailAlloc_6853_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6852_;
            }
            4 => {
                v___x_6859_ = lean_nat_dec_lt(v_detailed_6846_, v___x_6847_);
                crate::leanh::lean_dec(v_detailed_6846_);
                if v___x_6859_ == 0 {
                    crate::leanh::lean_dec_ref(v_thm_6843_);
                    crate::leanh::lean_dec(v_declName_6822_);
                    state = 2;
                    continue;
                } else {
                    v___x_6860_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(v_thm_6843_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_);
                    crate::leanh::lean_dec_ref(v_thm_6843_);
                    if crate::leanh::lean_obj_tag(v___x_6860_) == 0 {
                        v_a_6861_ = crate::leanh::lean_ctor_get(v___x_6860_, 0);
                        crate::leanh::lean_inc(v_a_6861_);
                        crate::leanh::lean_dec_ref_known(v___x_6860_, 1);
                        v___x_6862_ = l_Lean_MessageData_ofName(v_declName_6822_);
                        v___x_6863_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3);
                        v___x_6864_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6864_, 0, v___x_6862_);
                        crate::leanh::lean_ctor_set(v___x_6864_, 1, v___x_6863_);
                        v___x_6865_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6865_, 0, v___x_6864_);
                        crate::leanh::lean_ctor_set(v___x_6865_, 1, v_a_6861_);
                        v___x_6866_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_6865_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_);
                        if crate::leanh::lean_obj_tag(v___x_6866_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6866_, 1);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6847_);
                            crate::leanh::lean_dec(v_min_6845_);
                            crate::leanh::lean_del_object(v___x_6839_);
                            v_a_6867_ = crate::leanh::lean_ctor_get(v___x_6866_, 0);
                            v_isSharedCheck_6874_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6866_)) as u8;
                            if v_isSharedCheck_6874_ == 0 {
                                v___x_6869_ = v___x_6866_;
                                v_isShared_6870_ = v_isSharedCheck_6874_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6867_);
                                crate::leanh::lean_dec(v___x_6866_);
                                v___x_6869_ = crate::leanh::lean_box(0);
                                v_isShared_6870_ = v_isSharedCheck_6874_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6847_);
                        crate::leanh::lean_dec(v_min_6845_);
                        crate::leanh::lean_del_object(v___x_6839_);
                        crate::leanh::lean_dec(v_declName_6822_);
                        v_a_6875_ = crate::leanh::lean_ctor_get(v___x_6860_, 0);
                        v_isSharedCheck_6882_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6860_)) as u8;
                        if v_isSharedCheck_6882_ == 0 {
                            v___x_6877_ = v___x_6860_;
                            v_isShared_6878_ = v_isSharedCheck_6882_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6875_);
                            crate::leanh::lean_dec(v___x_6860_);
                            v___x_6877_ = crate::leanh::lean_box(0);
                            v_isShared_6878_ = v_isSharedCheck_6882_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_6870_ == 0 {
                    v___x_6872_ = v___x_6869_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6873_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6873_, 0, v_a_6867_);
                    v___x_6872_ = v_reuseFailAlloc_6873_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6872_;
            }
            7 => {
                if v_isShared_6878_ == 0 {
                    v___x_6880_ = v___x_6877_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6881_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6881_, 0, v_a_6875_);
                    v___x_6880_ = v_reuseFailAlloc_6881_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6880_;
            }
            9 => {
                if v_isShared_6900_ == 0 {
                    v___x_6902_ = v___x_6899_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6903_, 0, v_a_6897_);
                    v___x_6902_ = v_reuseFailAlloc_6903_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6902_;
            }
            11 => {
                if v_isShared_6920_ == 0 {
                    v___x_6922_ = v___x_6919_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6923_, 0, v_a_6917_);
                    v___x_6922_ = v_reuseFailAlloc_6923_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6922_;
            }
            13 => {
                if v_isShared_6929_ == 0 {
                    v___x_6931_ = v___x_6928_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6932_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6932_, 0, v_a_6926_);
                    v___x_6931_ = v_reuseFailAlloc_6932_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6931_;
            }
            15 => {
                if v_isShared_6937_ == 0 {
                    v___x_6939_ = v___x_6936_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6940_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6940_, 0, v_a_6934_);
                    v___x_6939_ = v_reuseFailAlloc_6940_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6939_;
            }
            17 => {
                if v_isShared_6945_ == 0 {
                    v___x_6947_ = v___x_6944_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6948_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6948_, 0, v_a_6942_);
                    v___x_6947_ = v_reuseFailAlloc_6948_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___boxed(
    mut v_declName_6950_: *mut crate::leanh::LeanObject,
    mut v_params_6951_: *mut crate::leanh::LeanObject,
    mut v_a_6952_: *mut crate::leanh::LeanObject,
    mut v_a_6953_: *mut crate::leanh::LeanObject,
    mut v_a_6954_: *mut crate::leanh::LeanObject,
    mut v_a_6955_: *mut crate::leanh::LeanObject,
    mut v_a_6956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6957_ =
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(
            v_declName_6950_,
            v_params_6951_,
            v_a_6952_,
            v_a_6953_,
            v_a_6954_,
            v_a_6955_,
        );
    crate::leanh::lean_dec(v_a_6955_);
    crate::leanh::lean_dec_ref(v_a_6954_);
    crate::leanh::lean_dec(v_a_6953_);
    crate::leanh::lean_dec_ref(v_a_6952_);
    return v_res_6957_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0(
    mut v_00_u03b1_6958_: *mut crate::leanh::LeanObject,
    mut v_name_6959_: *mut crate::leanh::LeanObject,
    mut v_bi_6960_: u8,
    mut v_type_6961_: *mut crate::leanh::LeanObject,
    mut v_k_6962_: *mut crate::leanh::LeanObject,
    mut v_kind_6963_: u8,
    mut v___y_6964_: *mut crate::leanh::LeanObject,
    mut v___y_6965_: *mut crate::leanh::LeanObject,
    mut v___y_6966_: *mut crate::leanh::LeanObject,
    mut v___y_6967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6969_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_6959_, v_bi_6960_, v_type_6961_, v_k_6962_, v_kind_6963_, v___y_6964_, v___y_6965_, v___y_6966_, v___y_6967_);
    return v___x_6969_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___boxed(
    mut v_00_u03b1_6970_: *mut crate::leanh::LeanObject,
    mut v_name_6971_: *mut crate::leanh::LeanObject,
    mut v_bi_6972_: *mut crate::leanh::LeanObject,
    mut v_type_6973_: *mut crate::leanh::LeanObject,
    mut v_k_6974_: *mut crate::leanh::LeanObject,
    mut v_kind_6975_: *mut crate::leanh::LeanObject,
    mut v___y_6976_: *mut crate::leanh::LeanObject,
    mut v___y_6977_: *mut crate::leanh::LeanObject,
    mut v___y_6978_: *mut crate::leanh::LeanObject,
    mut v___y_6979_: *mut crate::leanh::LeanObject,
    mut v___y_6980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_6981_: u8 = 0;
    let mut v_kind_boxed_6982_: u8 = 0;
    let mut v_res_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_6981_ = (crate::leanh::lean_unbox(v_bi_6972_) as u8);
    v_kind_boxed_6982_ = (crate::leanh::lean_unbox(v_kind_6975_) as u8);
    v_res_6983_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0(v_00_u03b1_6970_, v_name_6971_, v_bi_boxed_6981_, v_type_6973_, v_k_6974_, v_kind_boxed_6982_, v___y_6976_, v___y_6977_, v___y_6978_, v___y_6979_);
    crate::leanh::lean_dec(v___y_6979_);
    crate::leanh::lean_dec_ref(v___y_6978_);
    crate::leanh::lean_dec(v___y_6977_);
    crate::leanh::lean_dec_ref(v___y_6976_);
    return v_res_6983_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0(
    mut v_00_u03b1_6984_: *mut crate::leanh::LeanObject,
    mut v_name_6985_: *mut crate::leanh::LeanObject,
    mut v_type_6986_: *mut crate::leanh::LeanObject,
    mut v_k_6987_: *mut crate::leanh::LeanObject,
    mut v___y_6988_: *mut crate::leanh::LeanObject,
    mut v___y_6989_: *mut crate::leanh::LeanObject,
    mut v___y_6990_: *mut crate::leanh::LeanObject,
    mut v___y_6991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6993_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v_name_6985_, v_type_6986_, v_k_6987_, v___y_6988_, v___y_6989_, v___y_6990_, v___y_6991_);
    return v___x_6993_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___boxed(
    mut v_00_u03b1_6994_: *mut crate::leanh::LeanObject,
    mut v_name_6995_: *mut crate::leanh::LeanObject,
    mut v_type_6996_: *mut crate::leanh::LeanObject,
    mut v_k_6997_: *mut crate::leanh::LeanObject,
    mut v___y_6998_: *mut crate::leanh::LeanObject,
    mut v___y_6999_: *mut crate::leanh::LeanObject,
    mut v___y_7000_: *mut crate::leanh::LeanObject,
    mut v___y_7001_: *mut crate::leanh::LeanObject,
    mut v___y_7002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7003_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0(v_00_u03b1_6994_, v_name_6995_, v_type_6996_, v_k_6997_, v___y_6998_, v___y_6999_, v___y_7000_, v___y_7001_);
    crate::leanh::lean_dec(v___y_7001_);
    crate::leanh::lean_dec_ref(v___y_7000_);
    crate::leanh::lean_dec(v___y_6999_);
    crate::leanh::lean_dec_ref(v___y_6998_);
    return v_res_7003_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7005_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0);
    v___x_7006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7006_, 0, v___x_7005_);
    return v___x_7006_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg___boxed(
    mut v___y_7007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7008_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
    return v_res_7008_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0(
    mut v_00_u03b1_7009_: *mut crate::leanh::LeanObject,
    mut v___y_7010_: *mut crate::leanh::LeanObject,
    mut v___y_7011_: *mut crate::leanh::LeanObject,
    mut v___y_7012_: *mut crate::leanh::LeanObject,
    mut v___y_7013_: *mut crate::leanh::LeanObject,
    mut v___y_7014_: *mut crate::leanh::LeanObject,
    mut v___y_7015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7017_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
    return v___x_7017_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___boxed(
    mut v_00_u03b1_7018_: *mut crate::leanh::LeanObject,
    mut v___y_7019_: *mut crate::leanh::LeanObject,
    mut v___y_7020_: *mut crate::leanh::LeanObject,
    mut v___y_7021_: *mut crate::leanh::LeanObject,
    mut v___y_7022_: *mut crate::leanh::LeanObject,
    mut v___y_7023_: *mut crate::leanh::LeanObject,
    mut v___y_7024_: *mut crate::leanh::LeanObject,
    mut v___y_7025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7026_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0(v_00_u03b1_7018_, v___y_7019_, v___y_7020_, v___y_7021_, v___y_7022_, v___y_7023_, v___y_7024_);
    crate::leanh::lean_dec(v___y_7024_);
    crate::leanh::lean_dec_ref(v___y_7023_);
    crate::leanh::lean_dec(v___y_7022_);
    crate::leanh::lean_dec_ref(v___y_7021_);
    crate::leanh::lean_dec(v___y_7020_);
    crate::leanh::lean_dec_ref(v___y_7019_);
    return v_res_7026_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(
    mut v_a_7027_: *mut crate::leanh::LeanObject,
    mut v_as_7028_: *mut crate::leanh::LeanObject,
    mut v_sz_7029_: usize,
    mut v_i_7030_: usize,
    mut v_b_7031_: u8,
    mut v___y_7032_: *mut crate::leanh::LeanObject,
    mut v___y_7033_: *mut crate::leanh::LeanObject,
    mut v___y_7034_: *mut crate::leanh::LeanObject,
    mut v___y_7035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7037_: u8 = 0;
    let mut v___x_7038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7047_: u8 = 0;
    let mut v___x_7048_: usize = 0;
    let mut v___x_7049_: usize = 0;
    let mut v___x_7051_: u8 = 0;
    let mut v___x_7052_: u8 = 0;
    let mut v_a_7053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7056_: u8 = 0;
    let mut v___x_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7037_ = lean_usize_dec_lt(v_i_7030_, v_sz_7029_);
                if v___x_7037_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_7027_);
                    v___x_7038_ = crate::leanh::lean_box((v_b_7031_) as usize);
                    v___x_7039_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7039_, 0, v___x_7038_);
                    return v___x_7039_;
                } else {
                    v_a_7040_ = lean_array_uget_borrowed(v_as_7028_, v_i_7030_);
                    v___x_7041_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_7040_);
                    v___x_7042_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                        v_a_7040_,
                        v___x_7041_,
                        v___y_7034_,
                        v___y_7035_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7042_) == 0 {
                        v_a_7043_ = crate::leanh::lean_ctor_get(v___x_7042_, 0);
                        crate::leanh::lean_inc(v_a_7043_);
                        crate::leanh::lean_dec_ref_known(v___x_7042_, 1);
                        crate::leanh::lean_inc_ref(v_a_7027_);
                        v___x_7044_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_a_7043_, v_a_7027_, v___y_7032_, v___y_7033_, v___y_7034_, v___y_7035_);
                        if crate::leanh::lean_obj_tag(v___x_7044_) == 0 {
                            v_a_7045_ = crate::leanh::lean_ctor_get(v___x_7044_, 0);
                            crate::leanh::lean_inc(v_a_7045_);
                            crate::leanh::lean_dec_ref_known(v___x_7044_, 1);
                            v___x_7051_ = (crate::leanh::lean_unbox(v_a_7045_) as u8);
                            if v___x_7051_ == 0 {
                                crate::leanh::lean_dec(v_a_7045_);
                                v_a_7047_ = v_b_7031_;
                                state = 1;
                                continue;
                            } else {
                                v___x_7052_ = (crate::leanh::lean_unbox(v_a_7045_) as u8);
                                crate::leanh::lean_dec(v_a_7045_);
                                v_a_7047_ = v___x_7052_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_a_7027_);
                            return v___x_7044_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_7027_);
                        v_a_7053_ = crate::leanh::lean_ctor_get(v___x_7042_, 0);
                        v_isSharedCheck_7060_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7042_)) as u8;
                        if v_isSharedCheck_7060_ == 0 {
                            v___x_7055_ = v___x_7042_;
                            v_isShared_7056_ = v_isSharedCheck_7060_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7053_);
                            crate::leanh::lean_dec(v___x_7042_);
                            v___x_7055_ = crate::leanh::lean_box(0);
                            v_isShared_7056_ = v_isSharedCheck_7060_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7048_ = 1usize;
                v___x_7049_ = lean_usize_add(v_i_7030_, v___x_7048_);
                v_i_7030_ = v___x_7049_;
                v_b_7031_ = v_a_7047_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_7056_ == 0 {
                    v___x_7058_ = v___x_7055_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 0, v_a_7053_);
                    v___x_7058_ = v_reuseFailAlloc_7059_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg___boxed(
    mut v_a_7061_: *mut crate::leanh::LeanObject,
    mut v_as_7062_: *mut crate::leanh::LeanObject,
    mut v_sz_7063_: *mut crate::leanh::LeanObject,
    mut v_i_7064_: *mut crate::leanh::LeanObject,
    mut v_b_7065_: *mut crate::leanh::LeanObject,
    mut v___y_7066_: *mut crate::leanh::LeanObject,
    mut v___y_7067_: *mut crate::leanh::LeanObject,
    mut v___y_7068_: *mut crate::leanh::LeanObject,
    mut v___y_7069_: *mut crate::leanh::LeanObject,
    mut v___y_7070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7071_: usize = 0;
    let mut v_i_boxed_7072_: usize = 0;
    let mut v_b_boxed_7073_: u8 = 0;
    let mut v_res_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7071_ = crate::leanh::lean_unbox_usize(v_sz_7063_);
    crate::leanh::lean_dec(v_sz_7063_);
    v_i_boxed_7072_ = crate::leanh::lean_unbox_usize(v_i_7064_);
    crate::leanh::lean_dec(v_i_7064_);
    v_b_boxed_7073_ = (crate::leanh::lean_unbox(v_b_7065_) as u8);
    v_res_7074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_7061_, v_as_7062_, v_sz_boxed_7071_, v_i_boxed_7072_, v_b_boxed_7073_, v___y_7066_, v___y_7067_, v___y_7068_, v___y_7069_);
    crate::leanh::lean_dec(v___y_7069_);
    crate::leanh::lean_dec_ref(v___y_7068_);
    crate::leanh::lean_dec(v___y_7067_);
    crate::leanh::lean_dec_ref(v___y_7066_);
    crate::leanh::lean_dec_ref(v_as_7062_);
    return v_res_7074_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(
    mut v_sz_7082_: usize,
    mut v_i_7083_: usize,
    mut v_bs_7084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7085_: u8 = 0;
    let mut v___x_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: u8 = 0;
    let mut v___x_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7093_: usize = 0;
    let mut v___x_7094_: usize = 0;
    let mut v___x_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7085_ = lean_usize_dec_lt(v_i_7083_, v_sz_7082_);
                if v___x_7085_ == 0 {
                    v___x_7086_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7086_, 0, v_bs_7084_);
                    return v___x_7086_;
                } else {
                    v_v_7087_ = lean_array_uget(v_bs_7084_, v_i_7083_);
                    v___x_7088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2;
                    crate::leanh::lean_inc(v_v_7087_);
                    v___x_7089_ = l_Lean_Syntax_isOfKind(v_v_7087_, v___x_7088_);
                    if v___x_7089_ == 0 {
                        crate::leanh::lean_dec(v_v_7087_);
                        crate::leanh::lean_dec_ref(v_bs_7084_);
                        v___x_7090_ = crate::leanh::lean_box(0);
                        return v___x_7090_;
                    } else {
                        v___x_7091_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_7092_ = lean_array_uset(v_bs_7084_, v_i_7083_, v___x_7091_);
                        v___x_7093_ = 1usize;
                        v___x_7094_ = lean_usize_add(v_i_7083_, v___x_7093_);
                        v___x_7095_ = lean_array_uset(v_bs_x27_7092_, v_i_7083_, v_v_7087_);
                        v_i_7083_ = v___x_7094_;
                        v_bs_7084_ = v___x_7095_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___boxed(
    mut v_sz_7097_: *mut crate::leanh::LeanObject,
    mut v_i_7098_: *mut crate::leanh::LeanObject,
    mut v_bs_7099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7100_: usize = 0;
    let mut v_i_boxed_7101_: usize = 0;
    let mut v_res_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7100_ = crate::leanh::lean_unbox_usize(v_sz_7097_);
    crate::leanh::lean_dec(v_sz_7097_);
    v_i_boxed_7101_ = crate::leanh::lean_unbox_usize(v_i_7098_);
    crate::leanh::lean_dec(v_i_7098_);
    v_res_7102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_boxed_7100_, v_i_boxed_7101_, v_bs_7099_);
    return v_res_7102_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7118_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__9;
    v___x_7119_ = l_String_toRawSubstring_x27(v___x_7118_);
    return v___x_7119_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7123_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_7123_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0(
    mut v___x_7126_: u8,
    mut v_stx_7127_: *mut crate::leanh::LeanObject,
    mut v___x_7128_: *mut crate::leanh::LeanObject,
    mut v___y_7129_: *mut crate::leanh::LeanObject,
    mut v___y_7130_: *mut crate::leanh::LeanObject,
    mut v___y_7131_: *mut crate::leanh::LeanObject,
    mut v___y_7132_: *mut crate::leanh::LeanObject,
    mut v___y_7133_: *mut crate::leanh::LeanObject,
    mut v___y_7134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7148_: u8 = 0;
    let mut v_cancelTk_x3f_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7150_: u8 = 0;
    let mut v_inheritedTraceOptions_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7155_: usize = 0;
    let mut v___x_7156_: usize = 0;
    let mut v___x_7157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_7168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: u8 = 0;
    let mut v_sz_7170_: usize = 0;
    let mut v___x_7171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7175_: u8 = 0;
    let mut v___x_7176_: u8 = 0;
    let mut v___x_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_7181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7184_: u8 = 0;
    let mut v___x_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7209_: u8 = 0;
    let mut v___x_7210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7214_: u8 = 0;
    let mut v___x_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7219_: u8 = 0;
    let mut v_a_7220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7223_: u8 = 0;
    let mut v___x_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7227_: u8 = 0;
    let mut v_a_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7231_: u8 = 0;
    let mut v___x_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7235_: u8 = 0;
    let mut v_a_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7239_: u8 = 0;
    let mut v___x_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_7126_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_7128_);
                    crate::leanh::lean_dec(v_stx_7127_);
                    v___x_7136_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
                    return v___x_7136_;
                } else {
                    v_fileName_7137_ = crate::leanh::lean_ctor_get(v___y_7133_, 0);
                    v_fileMap_7138_ = crate::leanh::lean_ctor_get(v___y_7133_, 1);
                    v_options_7139_ = crate::leanh::lean_ctor_get(v___y_7133_, 2);
                    v_currRecDepth_7140_ = crate::leanh::lean_ctor_get(v___y_7133_, 3);
                    v_maxRecDepth_7141_ = crate::leanh::lean_ctor_get(v___y_7133_, 4);
                    v_ref_7142_ = crate::leanh::lean_ctor_get(v___y_7133_, 5);
                    v_currNamespace_7143_ = crate::leanh::lean_ctor_get(v___y_7133_, 6);
                    v_openDecls_7144_ = crate::leanh::lean_ctor_get(v___y_7133_, 7);
                    v_initHeartbeats_7145_ = crate::leanh::lean_ctor_get(v___y_7133_, 8);
                    v_quotContext_7146_ = crate::leanh::lean_ctor_get(v___y_7133_, 10);
                    v_currMacroScope_7147_ = crate::leanh::lean_ctor_get(v___y_7133_, 11);
                    v_diag_7148_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_7133_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_7149_ = crate::leanh::lean_ctor_get(v___y_7133_, 12);
                    v_suppressElabErrors_7150_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_7133_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_7151_ = crate::leanh::lean_ctor_get(v___y_7133_, 13);
                    v___x_7152_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_7153_ = l_Lean_Syntax_getArg(v_stx_7127_, v___x_7152_);
                    v___x_7154_ = l_Lean_Syntax_getArgs(v___x_7153_);
                    crate::leanh::lean_dec(v___x_7153_);
                    v_sz_7155_ = lean_array_size(v___x_7154_);
                    v___x_7156_ = 0usize;
                    v___x_7157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_7155_, v___x_7156_, v___x_7154_);
                    if crate::leanh::lean_obj_tag(v___x_7157_) == 0 {
                        crate::leanh::lean_dec_ref(v___x_7128_);
                        crate::leanh::lean_dec(v_stx_7127_);
                        v___x_7158_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
                        return v___x_7158_;
                    } else {
                        v_val_7159_ = crate::leanh::lean_ctor_get(v___x_7157_, 0);
                        crate::leanh::lean_inc(v_val_7159_);
                        crate::leanh::lean_dec_ref_known(v___x_7157_, 1);
                        v___x_7160_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc_ref(v_inheritedTraceOptions_7151_);
                        crate::leanh::lean_inc(v_cancelTk_x3f_7149_);
                        crate::leanh::lean_inc(v_currMacroScope_7147_);
                        crate::leanh::lean_inc(v_quotContext_7146_);
                        crate::leanh::lean_inc(v_initHeartbeats_7145_);
                        crate::leanh::lean_inc(v_openDecls_7144_);
                        crate::leanh::lean_inc(v_currNamespace_7143_);
                        crate::leanh::lean_inc(v_ref_7142_);
                        crate::leanh::lean_inc(v_maxRecDepth_7141_);
                        crate::leanh::lean_inc(v_currRecDepth_7140_);
                        crate::leanh::lean_inc_ref(v_options_7139_);
                        crate::leanh::lean_inc_ref(v_fileMap_7138_);
                        crate::leanh::lean_inc_ref(v_fileName_7137_);
                        v___x_7161_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                        crate::leanh::lean_ctor_set(v___x_7161_, 0, v_fileName_7137_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 1, v_fileMap_7138_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 2, v_options_7139_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 3, v_currRecDepth_7140_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 4, v_maxRecDepth_7141_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 5, v_ref_7142_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 6, v_currNamespace_7143_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 7, v_openDecls_7144_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 8, v_initHeartbeats_7145_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 9, v___x_7160_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 10, v_quotContext_7146_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 11, v_currMacroScope_7147_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 12, v_cancelTk_x3f_7149_);
                        crate::leanh::lean_ctor_set(v___x_7161_, 13, v_inheritedTraceOptions_7151_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7161_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                            v_diag_7148_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7161_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                            v_suppressElabErrors_7150_,
                        );
                        v___x_7162_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_val_7159_, v___y_7129_, v___x_7161_, v___y_7134_);
                        if crate::leanh::lean_obj_tag(v___x_7162_) == 0 {
                            v_a_7163_ = crate::leanh::lean_ctor_get(v___x_7162_, 0);
                            crate::leanh::lean_inc(v_a_7163_);
                            crate::leanh::lean_dec_ref_known(v___x_7162_, 1);
                            v___x_7164_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_a_7163_, v___y_7131_, v___y_7132_, v___x_7161_, v___y_7134_);
                            if crate::leanh::lean_obj_tag(v___x_7164_) == 0 {
                                v_a_7165_ = crate::leanh::lean_ctor_get(v___x_7164_, 0);
                                crate::leanh::lean_inc(v_a_7165_);
                                crate::leanh::lean_dec_ref_known(v___x_7164_, 1);
                                v___x_7166_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_7167_ = l_Lean_Syntax_getArg(v_stx_7127_, v___x_7166_);
                                v_ids_7168_ = l_Lean_Syntax_getArgs(v___x_7167_);
                                crate::leanh::lean_dec(v___x_7167_);
                                v___x_7169_ = 0;
                                v_sz_7170_ = lean_array_size(v_ids_7168_);
                                v___x_7171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_7165_, v_ids_7168_, v_sz_7170_, v___x_7156_, v___x_7169_, v___y_7131_, v___y_7132_, v___x_7161_, v___y_7134_);
                                crate::leanh::lean_dec_ref(v_ids_7168_);
                                if crate::leanh::lean_obj_tag(v___x_7171_) == 0 {
                                    v_a_7172_ = crate::leanh::lean_ctor_get(v___x_7171_, 0);
                                    v_isSharedCheck_7219_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_7171_)) as u8;
                                    if v_isSharedCheck_7219_ == 0 {
                                        v___x_7174_ = v___x_7171_;
                                        v_isShared_7175_ = v_isSharedCheck_7219_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_7172_);
                                        crate::leanh::lean_dec(v___x_7171_);
                                        v___x_7174_ = crate::leanh::lean_box(0);
                                        v_isShared_7175_ = v_isSharedCheck_7219_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_7161_, 14);
                                    crate::leanh::lean_dec_ref(v___x_7128_);
                                    crate::leanh::lean_dec(v_stx_7127_);
                                    v_a_7220_ = crate::leanh::lean_ctor_get(v___x_7171_, 0);
                                    v_isSharedCheck_7227_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_7171_)) as u8;
                                    if v_isSharedCheck_7227_ == 0 {
                                        v___x_7222_ = v___x_7171_;
                                        v_isShared_7223_ = v_isSharedCheck_7227_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_7220_);
                                        crate::leanh::lean_dec(v___x_7171_);
                                        v___x_7222_ = crate::leanh::lean_box(0);
                                        v_isShared_7223_ = v_isSharedCheck_7227_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_7161_, 14);
                                crate::leanh::lean_dec_ref(v___x_7128_);
                                crate::leanh::lean_dec(v_stx_7127_);
                                v_a_7228_ = crate::leanh::lean_ctor_get(v___x_7164_, 0);
                                v_isSharedCheck_7235_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7164_)) as u8;
                                if v_isSharedCheck_7235_ == 0 {
                                    v___x_7230_ = v___x_7164_;
                                    v_isShared_7231_ = v_isSharedCheck_7235_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7228_);
                                    crate::leanh::lean_dec(v___x_7164_);
                                    v___x_7230_ = crate::leanh::lean_box(0);
                                    v_isShared_7231_ = v_isSharedCheck_7235_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_7161_, 14);
                            crate::leanh::lean_dec_ref(v___x_7128_);
                            crate::leanh::lean_dec(v_stx_7127_);
                            v_a_7236_ = crate::leanh::lean_ctor_get(v___x_7162_, 0);
                            v_isSharedCheck_7243_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7162_)) as u8;
                            if v_isSharedCheck_7243_ == 0 {
                                v___x_7238_ = v___x_7162_;
                                v_isShared_7239_ = v_isSharedCheck_7243_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7236_);
                                crate::leanh::lean_dec(v___x_7162_);
                                v___x_7238_ = crate::leanh::lean_box(0);
                                v_isShared_7239_ = v_isSharedCheck_7243_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_7176_ = (crate::leanh::lean_unbox(v_a_7172_) as u8);
                crate::leanh::lean_dec(v_a_7172_);
                if v___x_7176_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_7161_, 14);
                    crate::leanh::lean_dec_ref(v___x_7128_);
                    crate::leanh::lean_dec(v_stx_7127_);
                    v___x_7177_ = crate::leanh::lean_box(0);
                    if v_isShared_7175_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7174_, 0, v___x_7177_);
                        v___x_7179_ = v___x_7174_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7180_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7180_, 0, v___x_7177_);
                        v___x_7179_ = v_reuseFailAlloc_7180_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_map_7181_ = crate::leanh::lean_ctor_get(v_options_7139_, 0);
                    v___x_7182_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3;
                    v___x_7212_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_7181_, v___x_7182_);
                    if crate::leanh::lean_obj_tag(v___x_7212_) == 0 {
                        crate::leanh::lean_del_object(v___x_7174_);
                        v___y_7184_ = v___x_7169_;
                        state = 3;
                        continue;
                    } else {
                        v_val_7213_ = crate::leanh::lean_ctor_get(v___x_7212_, 0);
                        crate::leanh::lean_inc(v_val_7213_);
                        crate::leanh::lean_dec_ref_known(v___x_7212_, 1);
                        if crate::leanh::lean_obj_tag(v_val_7213_) == 1 {
                            v_v_7214_ = crate::leanh::lean_ctor_get_uint8(v_val_7213_, 0 as u32);
                            crate::leanh::lean_dec_ref_known(v_val_7213_, 0);
                            if v_v_7214_ == 0 {
                                crate::leanh::lean_del_object(v___x_7174_);
                                v___y_7184_ = v_v_7214_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_7161_, 14);
                                crate::leanh::lean_dec_ref(v___x_7128_);
                                crate::leanh::lean_dec(v_stx_7127_);
                                v___x_7215_ = crate::leanh::lean_box(0);
                                if v_isShared_7175_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_7174_, 0, v___x_7215_);
                                    v___x_7217_ = v___x_7174_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7218_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7218_,
                                        0,
                                        v___x_7215_,
                                    );
                                    v___x_7217_ = v_reuseFailAlloc_7218_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_7213_);
                            crate::leanh::lean_del_object(v___x_7174_);
                            v___y_7184_ = v___x_7169_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_7179_;
            }
            3 => {
                v___x_7185_ = l_Lean_SourceInfo_fromRef(v_ref_7142_, v___y_7184_);
                v___x_7186_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5;
                v___x_7187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0;
                v___x_7188_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__6;
                v___x_7189_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__7;
                crate::leanh::lean_inc_ref(v___x_7128_);
                v___x_7190_ =
                    l_Lean_Name_mkStr4(v___x_7128_, v___x_7187_, v___x_7188_, v___x_7189_);
                v___x_7191_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__8;
                v___x_7192_ =
                    l_Lean_Name_mkStr4(v___x_7128_, v___x_7187_, v___x_7188_, v___x_7191_);
                crate::leanh::lean_inc_n(v___x_7185_, 6);
                v___x_7193_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7193_, 0, v___x_7185_);
                crate::leanh::lean_ctor_set(v___x_7193_, 1, v___x_7191_);
                v___x_7194_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10);
                v___x_7195_ = crate::leanh::lean_box(0);
                v___x_7196_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7196_, 0, v___x_7185_);
                crate::leanh::lean_ctor_set(v___x_7196_, 1, v___x_7194_);
                crate::leanh::lean_ctor_set(v___x_7196_, 2, v___x_7182_);
                crate::leanh::lean_ctor_set(v___x_7196_, 3, v___x_7195_);
                v___x_7197_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__12;
                v___x_7198_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13_once), _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13);
                v___x_7199_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7199_, 0, v___x_7185_);
                crate::leanh::lean_ctor_set(v___x_7199_, 1, v___x_7197_);
                crate::leanh::lean_ctor_set(v___x_7199_, 2, v___x_7198_);
                v___x_7200_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__14;
                v___x_7201_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7201_, 0, v___x_7185_);
                crate::leanh::lean_ctor_set(v___x_7201_, 1, v___x_7200_);
                v___x_7202_ = l_Lean_Syntax_node4(
                    v___x_7185_,
                    v___x_7192_,
                    v___x_7193_,
                    v___x_7196_,
                    v___x_7199_,
                    v___x_7201_,
                );
                v___x_7203_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7203_, 0, v___x_7185_);
                crate::leanh::lean_ctor_set(v___x_7203_, 1, v___x_7189_);
                crate::leanh::lean_inc(v_stx_7127_);
                v___x_7204_ = l_Lean_Syntax_node3(
                    v___x_7185_,
                    v___x_7190_,
                    v___x_7202_,
                    v___x_7203_,
                    v_stx_7127_,
                );
                v___x_7205_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7205_, 0, v___x_7186_);
                crate::leanh::lean_ctor_set(v___x_7205_, 1, v___x_7204_);
                v___x_7206_ = crate::leanh::lean_box(0);
                v___x_7207_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7207_, 0, v___x_7205_);
                crate::leanh::lean_ctor_set(v___x_7207_, 1, v___x_7206_);
                crate::leanh::lean_ctor_set(v___x_7207_, 2, v___x_7206_);
                crate::leanh::lean_ctor_set(v___x_7207_, 3, v___x_7206_);
                crate::leanh::lean_ctor_set(v___x_7207_, 4, v___x_7206_);
                crate::leanh::lean_ctor_set(v___x_7207_, 5, v___x_7206_);
                v___x_7208_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__15;
                v___x_7209_ = 4;
                v___x_7210_ = l_Lean_MessageData_nil;
                v___x_7211_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_stx_7127_,
                    v___x_7207_,
                    v___x_7206_,
                    v___x_7208_,
                    v___x_7206_,
                    v___x_7209_,
                    v___x_7210_,
                    v___x_7161_,
                    v___y_7134_,
                );
                crate::leanh::lean_dec_ref_known(v___x_7161_, 14);
                return v___x_7211_;
            }
            4 => {
                return v___x_7217_;
            }
            5 => {
                if v_isShared_7223_ == 0 {
                    v___x_7225_ = v___x_7222_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7226_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7226_, 0, v_a_7220_);
                    v___x_7225_ = v_reuseFailAlloc_7226_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7225_;
            }
            7 => {
                if v_isShared_7231_ == 0 {
                    v___x_7233_ = v___x_7230_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7234_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7234_, 0, v_a_7228_);
                    v___x_7233_ = v_reuseFailAlloc_7234_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7233_;
            }
            9 => {
                if v_isShared_7239_ == 0 {
                    v___x_7241_ = v___x_7238_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7242_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7242_, 0, v_a_7236_);
                    v___x_7241_ = v_reuseFailAlloc_7242_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___boxed(
    mut v___x_7244_: *mut crate::leanh::LeanObject,
    mut v_stx_7245_: *mut crate::leanh::LeanObject,
    mut v___x_7246_: *mut crate::leanh::LeanObject,
    mut v___y_7247_: *mut crate::leanh::LeanObject,
    mut v___y_7248_: *mut crate::leanh::LeanObject,
    mut v___y_7249_: *mut crate::leanh::LeanObject,
    mut v___y_7250_: *mut crate::leanh::LeanObject,
    mut v___y_7251_: *mut crate::leanh::LeanObject,
    mut v___y_7252_: *mut crate::leanh::LeanObject,
    mut v___y_7253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6343__boxed_7254_: u8 = 0;
    let mut v_res_7255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6343__boxed_7254_ = (crate::leanh::lean_unbox(v___x_7244_) as u8);
    v_res_7255_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0(v___x_6343__boxed_7254_, v_stx_7245_, v___x_7246_, v___y_7247_, v___y_7248_, v___y_7249_, v___y_7250_, v___y_7251_, v___y_7252_);
    crate::leanh::lean_dec(v___y_7252_);
    crate::leanh::lean_dec_ref(v___y_7251_);
    crate::leanh::lean_dec(v___y_7250_);
    crate::leanh::lean_dec_ref(v___y_7249_);
    crate::leanh::lean_dec(v___y_7248_);
    crate::leanh::lean_dec_ref(v___y_7247_);
    return v_res_7255_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect(
    mut v_stx_7261_: *mut crate::leanh::LeanObject,
    mut v_a_7262_: *mut crate::leanh::LeanObject,
    mut v_a_7263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: u8 = 0;
    let mut v___x_7268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7265_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_;
    v___x_7266_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1;
    crate::leanh::lean_inc(v_stx_7261_);
    v___x_7267_ = l_Lean_Syntax_isOfKind(v_stx_7261_, v___x_7266_);
    v___x_7268_ = crate::leanh::lean_box((v___x_7267_) as usize);
    v___f_7269_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
    crate::leanh::lean_closure_set(v___f_7269_, 0, v___x_7268_);
    crate::leanh::lean_closure_set(v___f_7269_, 1, v_stx_7261_);
    crate::leanh::lean_closure_set(v___f_7269_, 2, v___x_7265_);
    v___x_7270_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_7269_, v_a_7262_, v_a_7263_);
    return v___x_7270_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___boxed(
    mut v_stx_7271_: *mut crate::leanh::LeanObject,
    mut v_a_7272_: *mut crate::leanh::LeanObject,
    mut v_a_7273_: *mut crate::leanh::LeanObject,
    mut v_a_7274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7275_ =
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect(
            v_stx_7271_,
            v_a_7272_,
            v_a_7273_,
        );
    crate::leanh::lean_dec(v_a_7273_);
    crate::leanh::lean_dec_ref(v_a_7272_);
    return v_res_7275_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2(
    mut v_a_7276_: *mut crate::leanh::LeanObject,
    mut v_as_7277_: *mut crate::leanh::LeanObject,
    mut v_sz_7278_: usize,
    mut v_i_7279_: usize,
    mut v_b_7280_: u8,
    mut v___y_7281_: *mut crate::leanh::LeanObject,
    mut v___y_7282_: *mut crate::leanh::LeanObject,
    mut v___y_7283_: *mut crate::leanh::LeanObject,
    mut v___y_7284_: *mut crate::leanh::LeanObject,
    mut v___y_7285_: *mut crate::leanh::LeanObject,
    mut v___y_7286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_7276_, v_as_7277_, v_sz_7278_, v_i_7279_, v_b_7280_, v___y_7283_, v___y_7284_, v___y_7285_, v___y_7286_);
    return v___x_7288_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___boxed(
    mut v_a_7289_: *mut crate::leanh::LeanObject,
    mut v_as_7290_: *mut crate::leanh::LeanObject,
    mut v_sz_7291_: *mut crate::leanh::LeanObject,
    mut v_i_7292_: *mut crate::leanh::LeanObject,
    mut v_b_7293_: *mut crate::leanh::LeanObject,
    mut v___y_7294_: *mut crate::leanh::LeanObject,
    mut v___y_7295_: *mut crate::leanh::LeanObject,
    mut v___y_7296_: *mut crate::leanh::LeanObject,
    mut v___y_7297_: *mut crate::leanh::LeanObject,
    mut v___y_7298_: *mut crate::leanh::LeanObject,
    mut v___y_7299_: *mut crate::leanh::LeanObject,
    mut v___y_7300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7301_: usize = 0;
    let mut v_i_boxed_7302_: usize = 0;
    let mut v_b_boxed_7303_: u8 = 0;
    let mut v_res_7304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7301_ = crate::leanh::lean_unbox_usize(v_sz_7291_);
    crate::leanh::lean_dec(v_sz_7291_);
    v_i_boxed_7302_ = crate::leanh::lean_unbox_usize(v_i_7292_);
    crate::leanh::lean_dec(v_i_7292_);
    v_b_boxed_7303_ = (crate::leanh::lean_unbox(v_b_7293_) as u8);
    v_res_7304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2(v_a_7289_, v_as_7290_, v_sz_boxed_7301_, v_i_boxed_7302_, v_b_boxed_7303_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_, v___y_7298_, v___y_7299_);
    crate::leanh::lean_dec(v___y_7299_);
    crate::leanh::lean_dec_ref(v___y_7298_);
    crate::leanh::lean_dec(v___y_7297_);
    crate::leanh::lean_dec_ref(v___y_7296_);
    crate::leanh::lean_dec(v___y_7295_);
    crate::leanh::lean_dec_ref(v___y_7294_);
    crate::leanh::lean_dec_ref(v_as_7290_);
    return v_res_7304_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7310_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_7311_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1;
    v___x_7312_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__1;
    v___x_7313_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___boxed as *mut core::ffi::c_void, 4, 0);
    v___x_7314_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7310_,
        v___x_7311_,
        v___x_7312_,
        v___x_7313_,
    );
    return v___x_7314_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___boxed(
    mut v_a_7315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7316_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1();
    return v_res_7316_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(
    mut v_name_7317_: *mut crate::leanh::LeanObject,
    mut v_suff_7318_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_name_7317_) == 1 {
        let mut v_str_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7320_: u8 = 0;
        let mut v___x_7321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7324_: u8 = 0;
        v_str_7319_ = crate::leanh::lean_ctor_get(v_name_7317_, 1);
        v___x_7320_ = 1;
        v___x_7321_ = l_Lean_Name_toString(v_suff_7318_, v___x_7320_);
        v___x_7322_ = lean_string_utf8_byte_size(v_str_7319_);
        v___x_7323_ = lean_string_utf8_byte_size(v___x_7321_);
        v___x_7324_ = lean_nat_dec_le(v___x_7323_, v___x_7322_);
        if v___x_7324_ == 0 {
            crate::leanh::lean_dec_ref(v___x_7321_);
            return v___x_7324_;
        } else {
            let mut v___x_7325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7327_: u8 = 0;
            v___x_7325_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_7326_ = lean_nat_sub(v___x_7322_, v___x_7323_);
            v___x_7327_ = lean_string_memcmp(
                v_str_7319_,
                v___x_7321_,
                v___x_7326_,
                v___x_7325_,
                v___x_7323_,
            );
            crate::leanh::lean_dec(v___x_7326_);
            crate::leanh::lean_dec_ref(v___x_7321_);
            return v___x_7327_;
        }
    } else {
        let mut v___x_7328_: u8 = 0;
        crate::leanh::lean_dec(v_suff_7318_);
        v___x_7328_ = 0;
        return v___x_7328_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix___boxed(
    mut v_name_7329_: *mut crate::leanh::LeanObject,
    mut v_suff_7330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7331_: u8 = 0;
    let mut v_r_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7331_ =
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(
            v_name_7329_,
            v_suff_7330_,
        );
    crate::leanh::lean_dec(v_name_7329_);
    v_r_7332_ = crate::leanh::lean_box((v_res_7331_) as usize);
    return v_r_7332_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(
    mut v___x_7333_: *mut crate::leanh::LeanObject,
    mut v_as_7334_: *mut crate::leanh::LeanObject,
    mut v_i_7335_: usize,
    mut v_stop_7336_: usize,
) -> u8 {
    let mut v___x_7337_: u8 = 0;
    let mut v___x_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: u8 = 0;
    let mut v___x_7340_: usize = 0;
    let mut v___x_7341_: usize = 0;
    let mut v___x_7343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7337_ = lean_usize_dec_eq(v_i_7335_, v_stop_7336_);
                if v___x_7337_ == 0 {
                    v___x_7338_ = lean_array_uget_borrowed(v_as_7334_, v_i_7335_);
                    v___x_7339_ = l_Lean_Name_isPrefixOf(v___x_7338_, v___x_7333_);
                    if v___x_7339_ == 0 {
                        v___x_7340_ = 1usize;
                        v___x_7341_ = lean_usize_add(v_i_7335_, v___x_7340_);
                        v_i_7335_ = v___x_7341_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_7339_;
                    }
                } else {
                    v___x_7343_ = 0;
                    return v___x_7343_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1___boxed(
    mut v___x_7344_: *mut crate::leanh::LeanObject,
    mut v_as_7345_: *mut crate::leanh::LeanObject,
    mut v_i_7346_: *mut crate::leanh::LeanObject,
    mut v_stop_7347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_7348_: usize = 0;
    let mut v_stop_boxed_7349_: usize = 0;
    let mut v_res_7350_: u8 = 0;
    let mut v_r_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7348_ = crate::leanh::lean_unbox_usize(v_i_7346_);
    crate::leanh::lean_dec(v_i_7346_);
    v_stop_boxed_7349_ = crate::leanh::lean_unbox_usize(v_stop_7347_);
    crate::leanh::lean_dec(v_stop_7347_);
    v_res_7350_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(v___x_7344_, v_as_7345_, v_i_boxed_7348_, v_stop_boxed_7349_);
    crate::leanh::lean_dec_ref(v_as_7345_);
    crate::leanh::lean_dec(v___x_7344_);
    v_r_7351_ = crate::leanh::lean_box((v_res_7350_) as usize);
    return v_r_7351_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(
    mut v_declName_7355_: *mut crate::leanh::LeanObject,
    mut v_init_7356_: *mut crate::leanh::LeanObject,
    mut v_x_7357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7364_: u8 = 0;
    let mut v___x_7365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7366_: u8 = 0;
    let mut v___x_7367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7375_: u8 = 0;
    let mut v_unused_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7357_) == 0 {
                    v_k_7358_ = crate::leanh::lean_ctor_get(v_x_7357_, 1);
                    crate::leanh::lean_inc(v_k_7358_);
                    v_l_7359_ = crate::leanh::lean_ctor_get(v_x_7357_, 3);
                    crate::leanh::lean_inc(v_l_7359_);
                    v_r_7360_ = crate::leanh::lean_ctor_get(v_x_7357_, 4);
                    crate::leanh::lean_inc(v_r_7360_);
                    crate::leanh::lean_dec_ref_known(v_x_7357_, 5);
                    v___x_7361_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_7355_, v_init_7356_, v_l_7359_);
                    if crate::leanh::lean_obj_tag(v___x_7361_) == 0 {
                        crate::leanh::lean_dec(v_r_7360_);
                        crate::leanh::lean_dec(v_k_7358_);
                        return v___x_7361_;
                    } else {
                        v_isSharedCheck_7375_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7361_)) as u8;
                        if v_isSharedCheck_7375_ == 0 {
                            v_unused_7376_ = crate::leanh::lean_ctor_get(v___x_7361_, 0);
                            crate::leanh::lean_dec(v_unused_7376_);
                            v___x_7363_ = v___x_7361_;
                            v_isShared_7364_ = v_isSharedCheck_7375_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_7361_);
                            v___x_7363_ = crate::leanh::lean_box(0);
                            v_isShared_7364_ = v_isSharedCheck_7375_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_7377_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7377_, 0, v_init_7356_);
                    return v___x_7377_;
                }
            }
            1 => {
                v___x_7365_ = crate::leanh::lean_box(0);
                v___x_7366_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(v_declName_7355_, v_k_7358_);
                if v___x_7366_ == 0 {
                    crate::leanh::lean_del_object(v___x_7363_);
                    v___x_7367_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0;
                    v_init_7356_ = v___x_7367_;
                    v_x_7357_ = v_r_7360_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_7360_);
                    v___x_7369_ = crate::leanh::lean_box((v___x_7366_) as usize);
                    v___x_7370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7370_, 0, v___x_7369_);
                    v___x_7371_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7371_, 0, v___x_7370_);
                    crate::leanh::lean_ctor_set(v___x_7371_, 1, v___x_7365_);
                    if v_isShared_7364_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_7363_, 0);
                        crate::leanh::lean_ctor_set(v___x_7363_, 0, v___x_7371_);
                        v___x_7373_ = v___x_7363_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7374_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7374_, 0, v___x_7371_);
                        v___x_7373_ = v_reuseFailAlloc_7374_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___boxed(
    mut v_declName_7378_: *mut crate::leanh::LeanObject,
    mut v_init_7379_: *mut crate::leanh::LeanObject,
    mut v_x_7380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7381_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_7378_, v_init_7379_, v_x_7380_);
    crate::leanh::lean_dec(v_declName_7378_);
    return v_res_7381_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(
    mut v_declName_7385_: *mut crate::leanh::LeanObject,
    mut v_as_7386_: *mut crate::leanh::LeanObject,
    mut v_i_7387_: usize,
    mut v_stop_7388_: usize,
) -> u8 {
    let mut v___x_7389_: u8 = 0;
    let mut v___x_7390_: u8 = 0;
    let mut v___y_7392_: u8 = 0;
    let mut v___x_7393_: usize = 0;
    let mut v___x_7394_: usize = 0;
    let mut v___x_7396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7398_: u8 = 0;
    let mut v___x_7399_: u8 = 0;
    let mut v___x_7400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: u8 = 0;
    let mut v___x_7404_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7389_ = lean_usize_dec_eq(v_i_7387_, v_stop_7388_);
                if v___x_7389_ == 0 {
                    v___x_7390_ = 1;
                    v___x_7396_ = lean_array_uget_borrowed(v_as_7386_, v_i_7387_);
                    v___x_7397_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__1;
                    v___x_7398_ = lean_name_eq(v___x_7396_, v___x_7397_);
                    if v___x_7398_ == 0 {
                        v___x_7399_ = l_Lean_Name_isPrefixOf(v___x_7396_, v_declName_7385_);
                        v___y_7392_ = v___x_7399_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_declName_7385_);
                        v___x_7400_ = l_Lean_Name_components(v_declName_7385_);
                        v___x_7401_ = l_List_lengthTR___redArg(v___x_7400_);
                        crate::leanh::lean_dec(v___x_7400_);
                        v___x_7402_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7403_ = lean_nat_dec_eq(v___x_7401_, v___x_7402_);
                        crate::leanh::lean_dec(v___x_7401_);
                        v___y_7392_ = v___x_7403_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_7385_);
                    v___x_7404_ = 0;
                    return v___x_7404_;
                }
            }
            1 => {
                if v___y_7392_ == 0 {
                    v___x_7393_ = 1usize;
                    v___x_7394_ = lean_usize_add(v_i_7387_, v___x_7393_);
                    v_i_7387_ = v___x_7394_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_declName_7385_);
                    return v___x_7390_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___boxed(
    mut v_declName_7405_: *mut crate::leanh::LeanObject,
    mut v_as_7406_: *mut crate::leanh::LeanObject,
    mut v_i_7407_: *mut crate::leanh::LeanObject,
    mut v_stop_7408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_7409_: usize = 0;
    let mut v_stop_boxed_7410_: usize = 0;
    let mut v_res_7411_: u8 = 0;
    let mut v_r_7412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7409_ = crate::leanh::lean_unbox_usize(v_i_7407_);
    crate::leanh::lean_dec(v_i_7407_);
    v_stop_boxed_7410_ = crate::leanh::lean_unbox_usize(v_stop_7408_);
    crate::leanh::lean_dec(v_stop_7408_);
    v_res_7411_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(v_declName_7405_, v_as_7406_, v_i_boxed_7409_, v_stop_boxed_7410_);
    crate::leanh::lean_dec_ref(v_as_7406_);
    v_r_7412_ = crate::leanh::lean_box((v_res_7411_) as usize);
    return v_r_7412_;
}
pub unsafe fn l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(
    mut v_prefixes_x3f_7413_: *mut crate::leanh::LeanObject,
    mut v_inModule_7414_: u8,
    mut v___x_7415_: *mut crate::leanh::LeanObject,
    mut v___x_7416_: *mut crate::leanh::LeanObject,
    mut v___x_7417_: *mut crate::leanh::LeanObject,
    mut v_a_7418_: *mut crate::leanh::LeanObject,
    mut v_a_7419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_7421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_7427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7429_: u8 = 0;
    let mut v_val_7430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7433_: u8 = 0;
    let mut v___x_7436_: usize = 0;
    let mut v___x_7437_: usize = 0;
    let mut v___x_7438_: u8 = 0;
    let mut v_val_7440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: u8 = 0;
    let mut v___x_7448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7452_: usize = 0;
    let mut v___x_7453_: usize = 0;
    let mut v___x_7454_: u8 = 0;
    let mut v___x_7458_: u8 = 0;
    let mut v___y_7460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7463_: u8 = 0;
    let mut v___x_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_7418_) == 0 {
                    crate::leanh::lean_dec(v___x_7417_);
                    v___x_7420_ = lean_array_to_list(v_a_7419_);
                    return v___x_7420_;
                } else {
                    v_head_7421_ = crate::leanh::lean_ctor_get(v_a_7418_, 0);
                    crate::leanh::lean_inc(v_head_7421_);
                    v_tail_7422_ = crate::leanh::lean_ctor_get(v_a_7418_, 1);
                    crate::leanh::lean_inc(v_tail_7422_);
                    crate::leanh::lean_dec_ref_known(v_a_7418_, 2);
                    if crate::leanh::lean_obj_tag(v_head_7421_) == 0 {
                        v_declName_7427_ = crate::leanh::lean_ctor_get(v_head_7421_, 0);
                        crate::leanh::lean_inc(v_declName_7427_);
                        crate::leanh::lean_dec_ref_known(v_head_7421_, 1);
                        v___x_7458_ = l_Lean_NameSet_contains(v___x_7416_, v_declName_7427_);
                        if v___x_7458_ == 0 {
                            v___x_7464_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0;
                            crate::leanh::lean_inc(v___x_7417_);
                            v___x_7465_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_7427_, v___x_7464_, v___x_7417_);
                            v_a_7466_ = crate::leanh::lean_ctor_get(v___x_7465_, 0);
                            crate::leanh::lean_inc(v_a_7466_);
                            crate::leanh::lean_dec_ref(v___x_7465_);
                            v___y_7460_ = v_a_7466_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_declName_7427_);
                            v_a_7418_ = v_tail_7422_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_head_7421_);
                        v_a_7418_ = v_tail_7422_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7425_ = lean_array_push(v_a_7419_, v_val_7424_);
                v_a_7418_ = v_tail_7422_;
                v_a_7419_ = v___x_7425_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_7429_ == 0 {
                    if crate::leanh::lean_obj_tag(v_prefixes_x3f_7413_) == 1 {
                        if v_inModule_7414_ == 0 {
                            v_val_7430_ = crate::leanh::lean_ctor_get(v_prefixes_x3f_7413_, 0);
                            v___x_7431_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_7432_ = lean_array_get_size(v_val_7430_);
                            v___x_7433_ = lean_nat_dec_lt(v___x_7431_, v___x_7432_);
                            if v___x_7433_ == 0 {
                                crate::leanh::lean_dec(v_declName_7427_);
                                v_a_7418_ = v_tail_7422_;
                                state = 0;
                                continue;
                            } else {
                                if v___x_7433_ == 0 {
                                    crate::leanh::lean_dec(v_declName_7427_);
                                    v_a_7418_ = v_tail_7422_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_7436_ = 0usize;
                                    v___x_7437_ = lean_usize_of_nat(v___x_7432_);
                                    crate::leanh::lean_inc(v_declName_7427_);
                                    v___x_7438_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(v_declName_7427_, v_val_7430_, v___x_7436_, v___x_7437_);
                                    if v___x_7438_ == 0 {
                                        crate::leanh::lean_dec(v_declName_7427_);
                                        v_a_7418_ = v_tail_7422_;
                                        state = 0;
                                        continue;
                                    } else {
                                        v_val_7424_ = v_declName_7427_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v_val_7440_ = crate::leanh::lean_ctor_get(v_prefixes_x3f_7413_, 0);
                            v___x_7441_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v___x_7415_,
                                v_declName_7427_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_7441_) == 1 {
                                v_val_7442_ = crate::leanh::lean_ctor_get(v___x_7441_, 0);
                                crate::leanh::lean_inc(v_val_7442_);
                                crate::leanh::lean_dec_ref_known(v___x_7441_, 1);
                                v___x_7443_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_7444_ = lean_array_get_size(v_val_7440_);
                                v___x_7445_ = lean_nat_dec_lt(v___x_7443_, v___x_7444_);
                                if v___x_7445_ == 0 {
                                    crate::leanh::lean_dec(v_val_7442_);
                                    crate::leanh::lean_dec(v_declName_7427_);
                                    v_a_7418_ = v_tail_7422_;
                                    state = 0;
                                    continue;
                                } else {
                                    if v___x_7445_ == 0 {
                                        crate::leanh::lean_dec(v_val_7442_);
                                        crate::leanh::lean_dec(v_declName_7427_);
                                        v_a_7418_ = v_tail_7422_;
                                        state = 0;
                                        continue;
                                    } else {
                                        v___x_7448_ = crate::leanh::lean_box(0);
                                        v___x_7449_ = l_Lean_Environment_header(v___x_7415_);
                                        v___x_7450_ =
                                            l_Lean_EnvironmentHeader_moduleNames(v___x_7449_);
                                        v___x_7451_ =
                                            lean_array_get(v___x_7448_, v___x_7450_, v_val_7442_);
                                        crate::leanh::lean_dec(v_val_7442_);
                                        crate::leanh::lean_dec_ref(v___x_7450_);
                                        v___x_7452_ = 0usize;
                                        v___x_7453_ = lean_usize_of_nat(v___x_7444_);
                                        v___x_7454_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(v___x_7451_, v_val_7440_, v___x_7452_, v___x_7453_);
                                        crate::leanh::lean_dec(v___x_7451_);
                                        if v___x_7454_ == 0 {
                                            crate::leanh::lean_dec(v_declName_7427_);
                                            v_a_7418_ = v_tail_7422_;
                                            state = 0;
                                            continue;
                                        } else {
                                            v_val_7424_ = v_declName_7427_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_7441_);
                                crate::leanh::lean_dec(v_declName_7427_);
                                v_a_7418_ = v_tail_7422_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        v_val_7424_ = v_declName_7427_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_7427_);
                    v_a_7418_ = v_tail_7422_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                v_fst_7461_ = crate::leanh::lean_ctor_get(v___y_7460_, 0);
                crate::leanh::lean_inc(v_fst_7461_);
                crate::leanh::lean_dec_ref(v___y_7460_);
                if crate::leanh::lean_obj_tag(v_fst_7461_) == 0 {
                    v___y_7429_ = v___x_7458_;
                    state = 2;
                    continue;
                } else {
                    v_val_7462_ = crate::leanh::lean_ctor_get(v_fst_7461_, 0);
                    crate::leanh::lean_inc(v_val_7462_);
                    crate::leanh::lean_dec_ref_known(v_fst_7461_, 1);
                    v___x_7463_ = (crate::leanh::lean_unbox(v_val_7462_) as u8);
                    crate::leanh::lean_dec(v_val_7462_);
                    v___y_7429_ = v___x_7463_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3___boxed(
    mut v_prefixes_x3f_7469_: *mut crate::leanh::LeanObject,
    mut v_inModule_7470_: *mut crate::leanh::LeanObject,
    mut v___x_7471_: *mut crate::leanh::LeanObject,
    mut v___x_7472_: *mut crate::leanh::LeanObject,
    mut v___x_7473_: *mut crate::leanh::LeanObject,
    mut v_a_7474_: *mut crate::leanh::LeanObject,
    mut v_a_7475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inModule_boxed_7476_: u8 = 0;
    let mut v_res_7477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inModule_boxed_7476_ = (crate::leanh::lean_unbox(v_inModule_7470_) as u8);
    v_res_7477_ = l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(v_prefixes_x3f_7469_, v_inModule_boxed_7476_, v___x_7471_, v___x_7472_, v___x_7473_, v_a_7474_, v_a_7475_);
    crate::leanh::lean_dec(v___x_7472_);
    crate::leanh::lean_dec_ref(v___x_7471_);
    crate::leanh::lean_dec(v_prefixes_x3f_7469_);
    return v_res_7477_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(
    mut v_prefixes_x3f_7480_: *mut crate::leanh::LeanObject,
    mut v_inModule_7481_: u8,
    mut v_a_7482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_7488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_7489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7495_: u8 = 0;
    let mut v___x_7496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_7499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_7500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7512_: u8 = 0;
    let mut v_a_7513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7516_: u8 = 0;
    let mut v___x_7518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7520_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7484_ = lean_st_ref_get(v_a_7482_);
                v___x_7485_ = lean_st_ref_get(v_a_7482_);
                v_env_7486_ = crate::leanh::lean_ctor_get(v___x_7484_, 0);
                crate::leanh::lean_inc_ref(v_env_7486_);
                crate::leanh::lean_dec(v___x_7484_);
                v___x_7487_ =
                    l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
                v_toEnvExtension_7488_ = crate::leanh::lean_ctor_get(v___x_7487_, 0);
                v_asyncMode_7489_ = crate::leanh::lean_ctor_get(v_toEnvExtension_7488_, 2);
                v___x_7490_ = l_Lean_Meta_Grind_grindExt;
                v___x_7491_ =
                    l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_7490_, v_a_7482_);
                if crate::leanh::lean_obj_tag(v___x_7491_) == 0 {
                    v_a_7492_ = crate::leanh::lean_ctor_get(v___x_7491_, 0);
                    v_isSharedCheck_7512_ = (!crate::leanh::lean_is_exclusive(v___x_7491_)) as u8;
                    if v_isSharedCheck_7512_ == 0 {
                        v___x_7494_ = v___x_7491_;
                        v_isShared_7495_ = v_isSharedCheck_7512_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7492_);
                        crate::leanh::lean_dec(v___x_7491_);
                        v___x_7494_ = crate::leanh::lean_box(0);
                        v_isShared_7495_ = v_isSharedCheck_7512_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_7486_);
                    crate::leanh::lean_dec(v___x_7485_);
                    v_a_7513_ = crate::leanh::lean_ctor_get(v___x_7491_, 0);
                    v_isSharedCheck_7520_ = (!crate::leanh::lean_is_exclusive(v___x_7491_)) as u8;
                    if v_isSharedCheck_7520_ == 0 {
                        v___x_7515_ = v___x_7491_;
                        v_isShared_7516_ = v_isSharedCheck_7520_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7513_);
                        crate::leanh::lean_dec(v___x_7491_);
                        v___x_7515_ = crate::leanh::lean_box(0);
                        v_isShared_7516_ = v_isSharedCheck_7520_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7496_ = lean_st_ref_get(v_a_7482_);
                v_env_7497_ = crate::leanh::lean_ctor_get(v___x_7485_, 0);
                crate::leanh::lean_inc_ref(v_env_7497_);
                crate::leanh::lean_dec(v___x_7485_);
                v___x_7498_ =
                    l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
                v_toEnvExtension_7499_ = crate::leanh::lean_ctor_get(v___x_7498_, 0);
                v_asyncMode_7500_ = crate::leanh::lean_ctor_get(v_toEnvExtension_7499_, 2);
                v_env_7501_ = crate::leanh::lean_ctor_get(v___x_7496_, 0);
                crate::leanh::lean_inc_ref(v_env_7501_);
                crate::leanh::lean_dec(v___x_7496_);
                v___x_7502_ = crate::leanh::lean_box(1);
                v___x_7503_ = crate::leanh::lean_box(0);
                v___x_7504_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_7502_,
                    v___x_7487_,
                    v_env_7486_,
                    v_asyncMode_7489_,
                    v___x_7503_,
                );
                v___x_7505_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_7502_,
                    v___x_7498_,
                    v_env_7497_,
                    v_asyncMode_7500_,
                    v___x_7503_,
                );
                v___x_7506_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_a_7492_);
                crate::leanh::lean_dec(v_a_7492_);
                v___x_7507_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0;
                v___x_7508_ = l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(v_prefixes_x3f_7480_, v_inModule_7481_, v_env_7501_, v___x_7504_, v___x_7505_, v___x_7506_, v___x_7507_);
                crate::leanh::lean_dec(v___x_7504_);
                crate::leanh::lean_dec_ref(v_env_7501_);
                if v_isShared_7495_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7494_, 0, v___x_7508_);
                    v___x_7510_ = v___x_7494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7511_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7511_, 0, v___x_7508_);
                    v___x_7510_ = v_reuseFailAlloc_7511_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7510_;
            }
            3 => {
                if v_isShared_7516_ == 0 {
                    v___x_7518_ = v___x_7515_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7519_, 0, v_a_7513_);
                    v___x_7518_ = v_reuseFailAlloc_7519_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___boxed(
    mut v_prefixes_x3f_7521_: *mut crate::leanh::LeanObject,
    mut v_inModule_7522_: *mut crate::leanh::LeanObject,
    mut v_a_7523_: *mut crate::leanh::LeanObject,
    mut v_a_7524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inModule_boxed_7525_: u8 = 0;
    let mut v_res_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inModule_boxed_7525_ = (crate::leanh::lean_unbox(v_inModule_7522_) as u8);
    v_res_7526_ =
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(
            v_prefixes_x3f_7521_,
            v_inModule_boxed_7525_,
            v_a_7523_,
        );
    crate::leanh::lean_dec(v_a_7523_);
    crate::leanh::lean_dec(v_prefixes_x3f_7521_);
    return v_res_7526_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems(
    mut v_prefixes_x3f_7527_: *mut crate::leanh::LeanObject,
    mut v_inModule_7528_: u8,
    mut v_a_7529_: *mut crate::leanh::LeanObject,
    mut v_a_7530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7532_ =
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(
            v_prefixes_x3f_7527_,
            v_inModule_7528_,
            v_a_7530_,
        );
    return v___x_7532_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___boxed(
    mut v_prefixes_x3f_7533_: *mut crate::leanh::LeanObject,
    mut v_inModule_7534_: *mut crate::leanh::LeanObject,
    mut v_a_7535_: *mut crate::leanh::LeanObject,
    mut v_a_7536_: *mut crate::leanh::LeanObject,
    mut v_a_7537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inModule_boxed_7538_: u8 = 0;
    let mut v_res_7539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inModule_boxed_7538_ = (crate::leanh::lean_unbox(v_inModule_7534_) as u8);
    v_res_7539_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems(
        v_prefixes_x3f_7533_,
        v_inModule_boxed_7538_,
        v_a_7535_,
        v_a_7536_,
    );
    crate::leanh::lean_dec(v_a_7536_);
    crate::leanh::lean_dec_ref(v_a_7535_);
    crate::leanh::lean_dec(v_prefixes_x3f_7533_);
    return v_res_7539_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(
    mut v_sz_7540_: usize,
    mut v_i_7541_: usize,
    mut v_bs_7542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7543_: u8 = 0;
    let mut v_v_7544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7548_: usize = 0;
    let mut v___x_7549_: usize = 0;
    let mut v___x_7550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7543_ = lean_usize_dec_lt(v_i_7541_, v_sz_7540_);
                if v___x_7543_ == 0 {
                    return v_bs_7542_;
                } else {
                    v_v_7544_ = lean_array_uget(v_bs_7542_, v_i_7541_);
                    v___x_7545_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_7546_ = lean_array_uset(v_bs_7542_, v_i_7541_, v___x_7545_);
                    v___x_7547_ = l_Lean_TSyntax_getId(v_v_7544_);
                    crate::leanh::lean_dec(v_v_7544_);
                    v___x_7548_ = 1usize;
                    v___x_7549_ = lean_usize_add(v_i_7541_, v___x_7548_);
                    v___x_7550_ = lean_array_uset(v_bs_x27_7546_, v_i_7541_, v___x_7547_);
                    v_i_7541_ = v___x_7549_;
                    v_bs_7542_ = v___x_7550_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4___boxed(
    mut v_sz_7552_: *mut crate::leanh::LeanObject,
    mut v_i_7553_: *mut crate::leanh::LeanObject,
    mut v_bs_7554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7555_: usize = 0;
    let mut v_i_boxed_7556_: usize = 0;
    let mut v_res_7557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7555_ = crate::leanh::lean_unbox_usize(v_sz_7552_);
    crate::leanh::lean_dec(v_sz_7552_);
    v_i_boxed_7556_ = crate::leanh::lean_unbox_usize(v_i_7553_);
    crate::leanh::lean_dec(v_i_7553_);
    v_res_7557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(v_sz_boxed_7555_, v_i_boxed_7556_, v_bs_7554_);
    return v_res_7557_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(
    mut v_hi_7558_: *mut crate::leanh::LeanObject,
    mut v_pivot_7559_: *mut crate::leanh::LeanObject,
    mut v_as_7560_: *mut crate::leanh::LeanObject,
    mut v_i_7561_: *mut crate::leanh::LeanObject,
    mut v_k_7562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7563_: u8 = 0;
    let mut v___x_7564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: u8 = 0;
    let mut v___x_7568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7563_ = lean_nat_dec_lt(v_k_7562_, v_hi_7558_);
                if v___x_7563_ == 0 {
                    crate::leanh::lean_dec(v_k_7562_);
                    v___x_7564_ = lean_array_fswap(v_as_7560_, v_i_7561_, v_hi_7558_);
                    v___x_7565_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7565_, 0, v_i_7561_);
                    crate::leanh::lean_ctor_set(v___x_7565_, 1, v___x_7564_);
                    return v___x_7565_;
                } else {
                    v___x_7566_ = lean_array_fget_borrowed(v_as_7560_, v_k_7562_);
                    v___x_7567_ = l_Lean_Name_lt(v___x_7566_, v_pivot_7559_);
                    if v___x_7567_ == 0 {
                        v___x_7568_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7569_ = lean_nat_add(v_k_7562_, v___x_7568_);
                        crate::leanh::lean_dec(v_k_7562_);
                        v_k_7562_ = v___x_7569_;
                        state = 0;
                        continue;
                    } else {
                        v___x_7571_ = lean_array_fswap(v_as_7560_, v_i_7561_, v_k_7562_);
                        v___x_7572_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7573_ = lean_nat_add(v_i_7561_, v___x_7572_);
                        crate::leanh::lean_dec(v_i_7561_);
                        v___x_7574_ = lean_nat_add(v_k_7562_, v___x_7572_);
                        crate::leanh::lean_dec(v_k_7562_);
                        v_as_7560_ = v___x_7571_;
                        v_i_7561_ = v___x_7573_;
                        v_k_7562_ = v___x_7574_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg___boxed(
    mut v_hi_7576_: *mut crate::leanh::LeanObject,
    mut v_pivot_7577_: *mut crate::leanh::LeanObject,
    mut v_as_7578_: *mut crate::leanh::LeanObject,
    mut v_i_7579_: *mut crate::leanh::LeanObject,
    mut v_k_7580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7581_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_7576_, v_pivot_7577_, v_as_7578_, v_i_7579_, v_k_7580_);
    crate::leanh::lean_dec(v_pivot_7577_);
    crate::leanh::lean_dec(v_hi_7576_);
    return v_res_7581_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(
    mut v_n_7582_: *mut crate::leanh::LeanObject,
    mut v_as_7583_: *mut crate::leanh::LeanObject,
    mut v_lo_7584_: *mut crate::leanh::LeanObject,
    mut v_hi_7585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_7588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7592_: u8 = 0;
    let mut v___x_7593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7597_: u8 = 0;
    let mut v___x_7598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_7600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7605_: u8 = 0;
    let mut v___x_7606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7611_: u8 = 0;
    let mut v___x_7612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: u8 = 0;
    let mut v___x_7616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7597_ = lean_nat_dec_lt(v_lo_7584_, v_hi_7585_);
                if v___x_7597_ == 0 {
                    crate::leanh::lean_dec(v_lo_7584_);
                    return v_as_7583_;
                } else {
                    v___x_7598_ = lean_nat_add(v_lo_7584_, v_hi_7585_);
                    v___x_7599_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_7600_ = lean_nat_shiftr(v___x_7598_, v___x_7599_);
                    crate::leanh::lean_dec(v___x_7598_);
                    v___x_7613_ = lean_array_fget_borrowed(v_as_7583_, v_mid_7600_);
                    v___x_7614_ = lean_array_fget_borrowed(v_as_7583_, v_lo_7584_);
                    v___x_7615_ = l_Lean_Name_lt(v___x_7613_, v___x_7614_);
                    if v___x_7615_ == 0 {
                        v___y_7608_ = v_as_7583_;
                        state = 3;
                        continue;
                    } else {
                        v___x_7616_ = lean_array_fswap(v_as_7583_, v_lo_7584_, v_mid_7600_);
                        v___y_7608_ = v___x_7616_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_7588_ = lean_array_fget(v___y_7587_, v_hi_7585_);
                crate::leanh::lean_inc_n(v_lo_7584_, 2);
                v___x_7589_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_7585_, v_pivot_7588_, v___y_7587_, v_lo_7584_, v_lo_7584_);
                crate::leanh::lean_dec(v_pivot_7588_);
                v_fst_7590_ = crate::leanh::lean_ctor_get(v___x_7589_, 0);
                crate::leanh::lean_inc(v_fst_7590_);
                v_snd_7591_ = crate::leanh::lean_ctor_get(v___x_7589_, 1);
                crate::leanh::lean_inc(v_snd_7591_);
                crate::leanh::lean_dec_ref(v___x_7589_);
                v___x_7592_ = lean_nat_dec_le(v_hi_7585_, v_fst_7590_);
                if v___x_7592_ == 0 {
                    v___x_7593_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_7582_, v_snd_7591_, v_lo_7584_, v_fst_7590_);
                    v___x_7594_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7595_ = lean_nat_add(v_fst_7590_, v___x_7594_);
                    crate::leanh::lean_dec(v_fst_7590_);
                    v_as_7583_ = v___x_7593_;
                    v_lo_7584_ = v___x_7595_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_7590_);
                    crate::leanh::lean_dec(v_lo_7584_);
                    return v_snd_7591_;
                }
            }
            2 => {
                v___x_7603_ = lean_array_fget_borrowed(v___y_7602_, v_mid_7600_);
                v___x_7604_ = lean_array_fget_borrowed(v___y_7602_, v_hi_7585_);
                v___x_7605_ = l_Lean_Name_lt(v___x_7603_, v___x_7604_);
                if v___x_7605_ == 0 {
                    crate::leanh::lean_dec(v_mid_7600_);
                    v___y_7587_ = v___y_7602_;
                    state = 1;
                    continue;
                } else {
                    v___x_7606_ = lean_array_fswap(v___y_7602_, v_mid_7600_, v_hi_7585_);
                    crate::leanh::lean_dec(v_mid_7600_);
                    v___y_7587_ = v___x_7606_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_7609_ = lean_array_fget_borrowed(v___y_7608_, v_hi_7585_);
                v___x_7610_ = lean_array_fget_borrowed(v___y_7608_, v_lo_7584_);
                v___x_7611_ = l_Lean_Name_lt(v___x_7609_, v___x_7610_);
                if v___x_7611_ == 0 {
                    v___y_7602_ = v___y_7608_;
                    state = 2;
                    continue;
                } else {
                    v___x_7612_ = lean_array_fswap(v___y_7608_, v_lo_7584_, v_hi_7585_);
                    v___y_7602_ = v___x_7612_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg___boxed(
    mut v_n_7617_: *mut crate::leanh::LeanObject,
    mut v_as_7618_: *mut crate::leanh::LeanObject,
    mut v_lo_7619_: *mut crate::leanh::LeanObject,
    mut v_hi_7620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_7617_, v_as_7618_, v_lo_7619_, v_hi_7620_);
    crate::leanh::lean_dec(v_hi_7620_);
    crate::leanh::lean_dec(v_n_7617_);
    return v_res_7621_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(
    mut v_ref_7622_: *mut crate::leanh::LeanObject,
    mut v_msgData_7623_: *mut crate::leanh::LeanObject,
    mut v_severity_7624_: u8,
    mut v_isSilent_7625_: u8,
    mut v___y_7626_: *mut crate::leanh::LeanObject,
    mut v___y_7627_: *mut crate::leanh::LeanObject,
    mut v___y_7628_: *mut crate::leanh::LeanObject,
    mut v___y_7629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7632_: u8 = 0;
    let mut v___y_7633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7635_: u8 = 0;
    let mut v___y_7636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7655_: u8 = 0;
    let mut v___x_7656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7666_: u8 = 0;
    let mut v___y_7668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7669_: u8 = 0;
    let mut v___y_7670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7671_: u8 = 0;
    let mut v___y_7672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7673_: u8 = 0;
    let mut v___y_7674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7681_: u8 = 0;
    let mut v___x_7682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: u8 = 0;
    let mut v___x_7687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7691_: u8 = 0;
    let mut v___y_7693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7694_: u8 = 0;
    let mut v___y_7695_: u8 = 0;
    let mut v___y_7696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7698_: u8 = 0;
    let mut v___y_7699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7706_: u8 = 0;
    let mut v___y_7707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7708_: u8 = 0;
    let mut v___y_7709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7710_: u8 = 0;
    let mut v_ref_7711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: u8 = 0;
    let mut v___y_7717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7720_: u8 = 0;
    let mut v___y_7721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7722_: u8 = 0;
    let mut v___y_7723_: u8 = 0;
    let mut v___y_7725_: u8 = 0;
    let mut v_fileName_7726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7730_: u8 = 0;
    let mut v___x_7731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7734_: u8 = 0;
    let mut v___x_7735_: u8 = 0;
    let mut v___x_7736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: u8 = 0;
    let mut v___x_7738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7740_: u8 = 0;
    let mut v___x_7741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7715_ = 2;
                v___x_7740_ = l_Lean_instBEqMessageSeverity_beq(v_severity_7624_, v___x_7715_);
                if v___x_7740_ == 0 {
                    v___y_7725_ = v___x_7740_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_7623_);
                    v___x_7741_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_7623_);
                    v___y_7725_ = v___x_7741_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_7641_ = lean_st_ref_take(v___y_7640_);
                v_currNamespace_7642_ = crate::leanh::lean_ctor_get(v___y_7639_, 6);
                v_openDecls_7643_ = crate::leanh::lean_ctor_get(v___y_7639_, 7);
                v_env_7644_ = crate::leanh::lean_ctor_get(v___x_7641_, 0);
                v_nextMacroScope_7645_ = crate::leanh::lean_ctor_get(v___x_7641_, 1);
                v_ngen_7646_ = crate::leanh::lean_ctor_get(v___x_7641_, 2);
                v_auxDeclNGen_7647_ = crate::leanh::lean_ctor_get(v___x_7641_, 3);
                v_traceState_7648_ = crate::leanh::lean_ctor_get(v___x_7641_, 4);
                v_cache_7649_ = crate::leanh::lean_ctor_get(v___x_7641_, 5);
                v_messages_7650_ = crate::leanh::lean_ctor_get(v___x_7641_, 6);
                v_infoState_7651_ = crate::leanh::lean_ctor_get(v___x_7641_, 7);
                v_snapshotTasks_7652_ = crate::leanh::lean_ctor_get(v___x_7641_, 8);
                v_isSharedCheck_7666_ = (!crate::leanh::lean_is_exclusive(v___x_7641_)) as u8;
                if v_isSharedCheck_7666_ == 0 {
                    v___x_7654_ = v___x_7641_;
                    v_isShared_7655_ = v_isSharedCheck_7666_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_7652_);
                    crate::leanh::lean_inc(v_infoState_7651_);
                    crate::leanh::lean_inc(v_messages_7650_);
                    crate::leanh::lean_inc(v_cache_7649_);
                    crate::leanh::lean_inc(v_traceState_7648_);
                    crate::leanh::lean_inc(v_auxDeclNGen_7647_);
                    crate::leanh::lean_inc(v_ngen_7646_);
                    crate::leanh::lean_inc(v_nextMacroScope_7645_);
                    crate::leanh::lean_inc(v_env_7644_);
                    crate::leanh::lean_dec(v___x_7641_);
                    v___x_7654_ = crate::leanh::lean_box(0);
                    v_isShared_7655_ = v_isSharedCheck_7666_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_7643_);
                crate::leanh::lean_inc(v_currNamespace_7642_);
                v___x_7656_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7656_, 0, v_currNamespace_7642_);
                crate::leanh::lean_ctor_set(v___x_7656_, 1, v_openDecls_7643_);
                v___x_7657_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7657_, 0, v___x_7656_);
                crate::leanh::lean_ctor_set(v___x_7657_, 1, v___y_7638_);
                crate::leanh::lean_inc_ref(v___y_7633_);
                crate::leanh::lean_inc_ref(v___y_7637_);
                v___x_7658_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_7658_, 0, v___y_7637_);
                crate::leanh::lean_ctor_set(v___x_7658_, 1, v___y_7636_);
                crate::leanh::lean_ctor_set(v___x_7658_, 2, v___y_7634_);
                crate::leanh::lean_ctor_set(v___x_7658_, 3, v___y_7633_);
                crate::leanh::lean_ctor_set(v___x_7658_, 4, v___x_7657_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7658_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_7632_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7658_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_7635_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7658_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_7625_,
                );
                v___x_7659_ = l_Lean_MessageLog_add(v___x_7658_, v_messages_7650_);
                if v_isShared_7655_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7654_, 6, v___x_7659_);
                    v___x_7661_ = v___x_7654_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7665_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7665_, 0, v_env_7644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7665_, 1, v_nextMacroScope_7645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7665_, 2, v_ngen_7646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7665_, 3, v_auxDeclNGen_7647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7665_, 4, v_traceState_7648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7665_, 5, v_cache_7649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7665_, 6, v___x_7659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7665_, 7, v_infoState_7651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7665_, 8, v_snapshotTasks_7652_);
                    v___x_7661_ = v_reuseFailAlloc_7665_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7662_ = lean_st_ref_set(v___y_7640_, v___x_7661_);
                v___x_7663_ = crate::leanh::lean_box(0);
                v___x_7664_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7664_, 0, v___x_7663_);
                return v___x_7664_;
            }
            4 => {
                v___x_7676_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_7623_,
                    );
                v___x_7677_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v___x_7676_, v___y_7626_, v___y_7627_, v___y_7628_, v___y_7629_);
                v_a_7678_ = crate::leanh::lean_ctor_get(v___x_7677_, 0);
                v_isSharedCheck_7691_ = (!crate::leanh::lean_is_exclusive(v___x_7677_)) as u8;
                if v_isSharedCheck_7691_ == 0 {
                    v___x_7680_ = v___x_7677_;
                    v_isShared_7681_ = v_isSharedCheck_7691_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7678_);
                    crate::leanh::lean_dec(v___x_7677_);
                    v___x_7680_ = crate::leanh::lean_box(0);
                    v_isShared_7681_ = v_isSharedCheck_7691_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_7672_, 2);
                v___x_7682_ = l_Lean_FileMap_toPosition(v___y_7672_, v___y_7670_);
                crate::leanh::lean_dec(v___y_7670_);
                v___x_7683_ = l_Lean_FileMap_toPosition(v___y_7672_, v___y_7675_);
                crate::leanh::lean_dec(v___y_7675_);
                v___x_7684_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7684_, 0, v___x_7683_);
                v___x_7685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3;
                if v___y_7673_ == 0 {
                    crate::leanh::lean_del_object(v___x_7680_);
                    crate::leanh::lean_dec_ref(v___y_7668_);
                    v___y_7632_ = v___y_7669_;
                    v___y_7633_ = v___x_7685_;
                    v___y_7634_ = v___x_7684_;
                    v___y_7635_ = v___y_7671_;
                    v___y_7636_ = v___x_7682_;
                    v___y_7637_ = v___y_7674_;
                    v___y_7638_ = v_a_7678_;
                    v___y_7639_ = v___y_7628_;
                    v___y_7640_ = v___y_7629_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7678_);
                    v___x_7686_ = l_Lean_MessageData_hasTag(v___y_7668_, v_a_7678_);
                    if v___x_7686_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7684_, 1);
                        crate::leanh::lean_dec_ref(v___x_7682_);
                        crate::leanh::lean_dec(v_a_7678_);
                        v___x_7687_ = crate::leanh::lean_box(0);
                        if v_isShared_7681_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_7680_, 0, v___x_7687_);
                            v___x_7689_ = v___x_7680_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_7690_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7690_, 0, v___x_7687_);
                            v___x_7689_ = v_reuseFailAlloc_7690_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_7680_);
                        v___y_7632_ = v___y_7669_;
                        v___y_7633_ = v___x_7685_;
                        v___y_7634_ = v___x_7684_;
                        v___y_7635_ = v___y_7671_;
                        v___y_7636_ = v___x_7682_;
                        v___y_7637_ = v___y_7674_;
                        v___y_7638_ = v_a_7678_;
                        v___y_7639_ = v___y_7628_;
                        v___y_7640_ = v___y_7629_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_7689_;
            }
            7 => {
                v___x_7701_ = l_Lean_Syntax_getTailPos_x3f(v___y_7697_, v___y_7694_);
                crate::leanh::lean_dec(v___y_7697_);
                if crate::leanh::lean_obj_tag(v___x_7701_) == 0 {
                    crate::leanh::lean_inc(v___y_7700_);
                    v___y_7668_ = v___y_7693_;
                    v___y_7669_ = v___y_7694_;
                    v___y_7670_ = v___y_7700_;
                    v___y_7671_ = v___y_7695_;
                    v___y_7672_ = v___y_7696_;
                    v___y_7673_ = v___y_7698_;
                    v___y_7674_ = v___y_7699_;
                    v___y_7675_ = v___y_7700_;
                    state = 4;
                    continue;
                } else {
                    v_val_7702_ = crate::leanh::lean_ctor_get(v___x_7701_, 0);
                    crate::leanh::lean_inc(v_val_7702_);
                    crate::leanh::lean_dec_ref_known(v___x_7701_, 1);
                    v___y_7668_ = v___y_7693_;
                    v___y_7669_ = v___y_7694_;
                    v___y_7670_ = v___y_7700_;
                    v___y_7671_ = v___y_7695_;
                    v___y_7672_ = v___y_7696_;
                    v___y_7673_ = v___y_7698_;
                    v___y_7674_ = v___y_7699_;
                    v___y_7675_ = v_val_7702_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_7711_ = l_Lean_replaceRef(v_ref_7622_, v___y_7705_);
                v___x_7712_ = l_Lean_Syntax_getPos_x3f(v_ref_7711_, v___y_7706_);
                if crate::leanh::lean_obj_tag(v___x_7712_) == 0 {
                    v___x_7713_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7693_ = v___y_7704_;
                    v___y_7694_ = v___y_7706_;
                    v___y_7695_ = v___y_7710_;
                    v___y_7696_ = v___y_7707_;
                    v___y_7697_ = v_ref_7711_;
                    v___y_7698_ = v___y_7708_;
                    v___y_7699_ = v___y_7709_;
                    v___y_7700_ = v___x_7713_;
                    state = 7;
                    continue;
                } else {
                    v_val_7714_ = crate::leanh::lean_ctor_get(v___x_7712_, 0);
                    crate::leanh::lean_inc(v_val_7714_);
                    crate::leanh::lean_dec_ref_known(v___x_7712_, 1);
                    v___y_7693_ = v___y_7704_;
                    v___y_7694_ = v___y_7706_;
                    v___y_7695_ = v___y_7710_;
                    v___y_7696_ = v___y_7707_;
                    v___y_7697_ = v_ref_7711_;
                    v___y_7698_ = v___y_7708_;
                    v___y_7699_ = v___y_7709_;
                    v___y_7700_ = v_val_7714_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_7723_ == 0 {
                    v___y_7704_ = v___y_7718_;
                    v___y_7705_ = v___y_7717_;
                    v___y_7706_ = v___y_7722_;
                    v___y_7707_ = v___y_7719_;
                    v___y_7708_ = v___y_7720_;
                    v___y_7709_ = v___y_7721_;
                    v___y_7710_ = v_severity_7624_;
                    state = 8;
                    continue;
                } else {
                    v___y_7704_ = v___y_7718_;
                    v___y_7705_ = v___y_7717_;
                    v___y_7706_ = v___y_7722_;
                    v___y_7707_ = v___y_7719_;
                    v___y_7708_ = v___y_7720_;
                    v___y_7709_ = v___y_7721_;
                    v___y_7710_ = v___x_7715_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_7725_ == 0 {
                    v_fileName_7726_ = crate::leanh::lean_ctor_get(v___y_7628_, 0);
                    v_fileMap_7727_ = crate::leanh::lean_ctor_get(v___y_7628_, 1);
                    v_options_7728_ = crate::leanh::lean_ctor_get(v___y_7628_, 2);
                    v_ref_7729_ = crate::leanh::lean_ctor_get(v___y_7628_, 5);
                    v_suppressElabErrors_7730_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_7628_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_7731_ = crate::leanh::lean_box((v___y_7725_) as usize);
                    v___x_7732_ = crate::leanh::lean_box((v_suppressElabErrors_7730_) as usize);
                    v___f_7733_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_7733_, 0, v___x_7731_);
                    crate::leanh::lean_closure_set(v___f_7733_, 1, v___x_7732_);
                    v___x_7734_ = 1;
                    v___x_7735_ = l_Lean_instBEqMessageSeverity_beq(v_severity_7624_, v___x_7734_);
                    if v___x_7735_ == 0 {
                        v___y_7717_ = v_ref_7729_;
                        v___y_7718_ = v___f_7733_;
                        v___y_7719_ = v_fileMap_7727_;
                        v___y_7720_ = v_suppressElabErrors_7730_;
                        v___y_7721_ = v_fileName_7726_;
                        v___y_7722_ = v___y_7725_;
                        v___y_7723_ = v___x_7735_;
                        state = 9;
                        continue;
                    } else {
                        v___x_7736_ = l_Lean_warningAsError;
                        v___x_7737_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(v_options_7728_, v___x_7736_);
                        v___y_7717_ = v_ref_7729_;
                        v___y_7718_ = v___f_7733_;
                        v___y_7719_ = v_fileMap_7727_;
                        v___y_7720_ = v_suppressElabErrors_7730_;
                        v___y_7721_ = v_fileName_7726_;
                        v___y_7722_ = v___y_7725_;
                        v___y_7723_ = v___x_7737_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_7623_);
                    v___x_7738_ = crate::leanh::lean_box(0);
                    v___x_7739_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7739_, 0, v___x_7738_);
                    return v___x_7739_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_7742_: *mut crate::leanh::LeanObject,
    mut v_msgData_7743_: *mut crate::leanh::LeanObject,
    mut v_severity_7744_: *mut crate::leanh::LeanObject,
    mut v_isSilent_7745_: *mut crate::leanh::LeanObject,
    mut v___y_7746_: *mut crate::leanh::LeanObject,
    mut v___y_7747_: *mut crate::leanh::LeanObject,
    mut v___y_7748_: *mut crate::leanh::LeanObject,
    mut v___y_7749_: *mut crate::leanh::LeanObject,
    mut v___y_7750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_7751_: u8 = 0;
    let mut v_isSilent_boxed_7752_: u8 = 0;
    let mut v_res_7753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_7751_ = (crate::leanh::lean_unbox(v_severity_7744_) as u8);
    v_isSilent_boxed_7752_ = (crate::leanh::lean_unbox(v_isSilent_7745_) as u8);
    v_res_7753_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_7742_, v_msgData_7743_, v_severity_boxed_7751_, v_isSilent_boxed_7752_, v___y_7746_, v___y_7747_, v___y_7748_, v___y_7749_);
    crate::leanh::lean_dec(v___y_7749_);
    crate::leanh::lean_dec_ref(v___y_7748_);
    crate::leanh::lean_dec(v___y_7747_);
    crate::leanh::lean_dec_ref(v___y_7746_);
    crate::leanh::lean_dec(v_ref_7742_);
    return v_res_7753_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(
    mut v_msgData_7754_: *mut crate::leanh::LeanObject,
    mut v_severity_7755_: u8,
    mut v_isSilent_7756_: u8,
    mut v___y_7757_: *mut crate::leanh::LeanObject,
    mut v___y_7758_: *mut crate::leanh::LeanObject,
    mut v___y_7759_: *mut crate::leanh::LeanObject,
    mut v___y_7760_: *mut crate::leanh::LeanObject,
    mut v___y_7761_: *mut crate::leanh::LeanObject,
    mut v___y_7762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_7764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_7764_ = crate::leanh::lean_ctor_get(v___y_7761_, 5);
    v___x_7765_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_7764_, v_msgData_7754_, v_severity_7755_, v_isSilent_7756_, v___y_7759_, v___y_7760_, v___y_7761_, v___y_7762_);
    return v___x_7765_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0___boxed(
    mut v_msgData_7766_: *mut crate::leanh::LeanObject,
    mut v_severity_7767_: *mut crate::leanh::LeanObject,
    mut v_isSilent_7768_: *mut crate::leanh::LeanObject,
    mut v___y_7769_: *mut crate::leanh::LeanObject,
    mut v___y_7770_: *mut crate::leanh::LeanObject,
    mut v___y_7771_: *mut crate::leanh::LeanObject,
    mut v___y_7772_: *mut crate::leanh::LeanObject,
    mut v___y_7773_: *mut crate::leanh::LeanObject,
    mut v___y_7774_: *mut crate::leanh::LeanObject,
    mut v___y_7775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_7776_: u8 = 0;
    let mut v_isSilent_boxed_7777_: u8 = 0;
    let mut v_res_7778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_7776_ = (crate::leanh::lean_unbox(v_severity_7767_) as u8);
    v_isSilent_boxed_7777_ = (crate::leanh::lean_unbox(v_isSilent_7768_) as u8);
    v_res_7778_ = l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(v_msgData_7766_, v_severity_boxed_7776_, v_isSilent_boxed_7777_, v___y_7769_, v___y_7770_, v___y_7771_, v___y_7772_, v___y_7773_, v___y_7774_);
    crate::leanh::lean_dec(v___y_7774_);
    crate::leanh::lean_dec_ref(v___y_7773_);
    crate::leanh::lean_dec(v___y_7772_);
    crate::leanh::lean_dec_ref(v___y_7771_);
    crate::leanh::lean_dec(v___y_7770_);
    crate::leanh::lean_dec_ref(v___y_7769_);
    return v_res_7778_;
}
pub unsafe fn l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(
    mut v_msgData_7779_: *mut crate::leanh::LeanObject,
    mut v___y_7780_: *mut crate::leanh::LeanObject,
    mut v___y_7781_: *mut crate::leanh::LeanObject,
    mut v___y_7782_: *mut crate::leanh::LeanObject,
    mut v___y_7783_: *mut crate::leanh::LeanObject,
    mut v___y_7784_: *mut crate::leanh::LeanObject,
    mut v___y_7785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7787_: u8 = 0;
    let mut v___x_7788_: u8 = 0;
    let mut v___x_7789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7787_ = 2;
    v___x_7788_ = 0;
    v___x_7789_ = l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(v_msgData_7779_, v___x_7787_, v___x_7788_, v___y_7780_, v___y_7781_, v___y_7782_, v___y_7783_, v___y_7784_, v___y_7785_);
    return v___x_7789_;
}
pub unsafe fn l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0___boxed(
    mut v_msgData_7790_: *mut crate::leanh::LeanObject,
    mut v___y_7791_: *mut crate::leanh::LeanObject,
    mut v___y_7792_: *mut crate::leanh::LeanObject,
    mut v___y_7793_: *mut crate::leanh::LeanObject,
    mut v___y_7794_: *mut crate::leanh::LeanObject,
    mut v___y_7795_: *mut crate::leanh::LeanObject,
    mut v___y_7796_: *mut crate::leanh::LeanObject,
    mut v___y_7797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7798_ = l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(v_msgData_7790_, v___y_7791_, v___y_7792_, v___y_7793_, v___y_7794_, v___y_7795_, v___y_7796_);
    crate::leanh::lean_dec(v___y_7796_);
    crate::leanh::lean_dec_ref(v___y_7795_);
    crate::leanh::lean_dec(v___y_7794_);
    crate::leanh::lean_dec_ref(v___y_7793_);
    crate::leanh::lean_dec(v___y_7792_);
    crate::leanh::lean_dec_ref(v___y_7791_);
    return v_res_7798_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__0;
    v___x_7801_ = l_Lean_stringToMessageData(v___x_7800_);
    return v___x_7801_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(
    mut v_a_7802_: *mut crate::leanh::LeanObject,
    mut v_as_7803_: *mut crate::leanh::LeanObject,
    mut v_sz_7804_: usize,
    mut v_i_7805_: usize,
    mut v_b_7806_: *mut crate::leanh::LeanObject,
    mut v___y_7807_: *mut crate::leanh::LeanObject,
    mut v___y_7808_: *mut crate::leanh::LeanObject,
    mut v___y_7809_: *mut crate::leanh::LeanObject,
    mut v___y_7810_: *mut crate::leanh::LeanObject,
    mut v___y_7811_: *mut crate::leanh::LeanObject,
    mut v___y_7812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_7815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7816_: usize = 0;
    let mut v___x_7817_: usize = 0;
    let mut v___x_7819_: u8 = 0;
    let mut v___x_7820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7824_: u8 = 0;
    let mut v___x_7825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7829_: u8 = 0;
    let mut v___y_7831_: u8 = 0;
    let mut v___x_7832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7841_: u8 = 0;
    let mut v___x_7843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7845_: u8 = 0;
    let mut v___x_7847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7849_: u8 = 0;
    let mut v___x_7850_: u8 = 0;
    let mut v_isSharedCheck_7851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7819_ = lean_usize_dec_lt(v_i_7805_, v_sz_7804_);
                if v___x_7819_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_7802_);
                    v___x_7820_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7820_, 0, v_b_7806_);
                    return v___x_7820_;
                } else {
                    v_a_7821_ = lean_array_uget_borrowed(v_as_7803_, v_i_7805_);
                    crate::leanh::lean_inc_ref(v_a_7802_);
                    crate::leanh::lean_inc(v_a_7821_);
                    v___x_7822_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_a_7821_, v_a_7802_, v___y_7809_, v___y_7810_, v___y_7811_, v___y_7812_);
                    if crate::leanh::lean_obj_tag(v___x_7822_) == 0 {
                        v_a_7823_ = crate::leanh::lean_ctor_get(v___x_7822_, 0);
                        crate::leanh::lean_inc(v_a_7823_);
                        crate::leanh::lean_dec_ref_known(v___x_7822_, 1);
                        v___x_7824_ = (crate::leanh::lean_unbox(v_a_7823_) as u8);
                        crate::leanh::lean_dec(v_a_7823_);
                        if v___x_7824_ == 0 {
                            v_snd_7815_ = v_b_7806_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7821_);
                            v___x_7825_ = lean_array_push(v_b_7806_, v_a_7821_);
                            v_snd_7815_ = v___x_7825_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7826_ = crate::leanh::lean_ctor_get(v___x_7822_, 0);
                        v_isSharedCheck_7851_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7822_)) as u8;
                        if v_isSharedCheck_7851_ == 0 {
                            v___x_7828_ = v___x_7822_;
                            v_isShared_7829_ = v_isSharedCheck_7851_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7826_);
                            crate::leanh::lean_dec(v___x_7822_);
                            v___x_7828_ = crate::leanh::lean_box(0);
                            v_isShared_7829_ = v_isSharedCheck_7851_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7816_ = 1usize;
                v___x_7817_ = lean_usize_add(v_i_7805_, v___x_7816_);
                v_i_7805_ = v___x_7817_;
                v_b_7806_ = v_snd_7815_;
                state = 0;
                continue;
            }
            2 => {
                v___x_7849_ = l_Lean_Exception_isInterrupt(v_a_7826_);
                if v___x_7849_ == 0 {
                    crate::leanh::lean_inc(v_a_7826_);
                    v___x_7850_ = l_Lean_Exception_isRuntime(v_a_7826_);
                    v___y_7831_ = v___x_7850_;
                    state = 3;
                    continue;
                } else {
                    v___y_7831_ = v___x_7849_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_7831_ == 0 {
                    crate::leanh::lean_del_object(v___x_7828_);
                    crate::leanh::lean_inc(v_a_7821_);
                    v___x_7832_ = l_Lean_MessageData_ofName(v_a_7821_);
                    v___x_7833_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1);
                    v___x_7834_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7834_, 0, v___x_7832_);
                    crate::leanh::lean_ctor_set(v___x_7834_, 1, v___x_7833_);
                    v___x_7835_ = l_Lean_Exception_toMessageData(v_a_7826_);
                    v___x_7836_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7836_, 0, v___x_7834_);
                    crate::leanh::lean_ctor_set(v___x_7836_, 1, v___x_7835_);
                    v___x_7837_ = l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(v___x_7836_, v___y_7807_, v___y_7808_, v___y_7809_, v___y_7810_, v___y_7811_, v___y_7812_);
                    if crate::leanh::lean_obj_tag(v___x_7837_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7837_, 1);
                        v_snd_7815_ = v_b_7806_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_7806_);
                        crate::leanh::lean_dec_ref(v_a_7802_);
                        v_a_7838_ = crate::leanh::lean_ctor_get(v___x_7837_, 0);
                        v_isSharedCheck_7845_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7837_)) as u8;
                        if v_isSharedCheck_7845_ == 0 {
                            v___x_7840_ = v___x_7837_;
                            v_isShared_7841_ = v_isSharedCheck_7845_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7838_);
                            crate::leanh::lean_dec(v___x_7837_);
                            v___x_7840_ = crate::leanh::lean_box(0);
                            v_isShared_7841_ = v_isSharedCheck_7845_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_7806_);
                    crate::leanh::lean_dec_ref(v_a_7802_);
                    if v_isShared_7829_ == 0 {
                        v___x_7847_ = v___x_7828_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7848_, 0, v_a_7826_);
                        v___x_7847_ = v_reuseFailAlloc_7848_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_7841_ == 0 {
                    v___x_7843_ = v___x_7840_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7844_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7844_, 0, v_a_7838_);
                    v___x_7843_ = v_reuseFailAlloc_7844_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7843_;
            }
            6 => {
                return v___x_7847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___boxed(
    mut v_a_7852_: *mut crate::leanh::LeanObject,
    mut v_as_7853_: *mut crate::leanh::LeanObject,
    mut v_sz_7854_: *mut crate::leanh::LeanObject,
    mut v_i_7855_: *mut crate::leanh::LeanObject,
    mut v_b_7856_: *mut crate::leanh::LeanObject,
    mut v___y_7857_: *mut crate::leanh::LeanObject,
    mut v___y_7858_: *mut crate::leanh::LeanObject,
    mut v___y_7859_: *mut crate::leanh::LeanObject,
    mut v___y_7860_: *mut crate::leanh::LeanObject,
    mut v___y_7861_: *mut crate::leanh::LeanObject,
    mut v___y_7862_: *mut crate::leanh::LeanObject,
    mut v___y_7863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7864_: usize = 0;
    let mut v_i_boxed_7865_: usize = 0;
    let mut v_res_7866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7864_ = crate::leanh::lean_unbox_usize(v_sz_7854_);
    crate::leanh::lean_dec(v_sz_7854_);
    v_i_boxed_7865_ = crate::leanh::lean_unbox_usize(v_i_7855_);
    crate::leanh::lean_dec(v_i_7855_);
    v_res_7866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(v_a_7852_, v_as_7853_, v_sz_boxed_7864_, v_i_boxed_7865_, v_b_7856_, v___y_7857_, v___y_7858_, v___y_7859_, v___y_7860_, v___y_7861_, v___y_7862_);
    crate::leanh::lean_dec(v___y_7862_);
    crate::leanh::lean_dec_ref(v___y_7861_);
    crate::leanh::lean_dec(v___y_7860_);
    crate::leanh::lean_dec_ref(v___y_7859_);
    crate::leanh::lean_dec(v___y_7858_);
    crate::leanh::lean_dec_ref(v___y_7857_);
    crate::leanh::lean_dec_ref(v_as_7853_);
    return v_res_7866_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(
    mut v_as_7868_: *mut crate::leanh::LeanObject,
    mut v_sz_7869_: usize,
    mut v_i_7870_: usize,
    mut v_b_7871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7873_: u8 = 0;
    let mut v___x_7874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7882_: usize = 0;
    let mut v___x_7883_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7873_ = lean_usize_dec_lt(v_i_7870_, v_sz_7869_);
                if v___x_7873_ == 0 {
                    v___x_7874_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7874_, 0, v_b_7871_);
                    return v___x_7874_;
                } else {
                    v___x_7875_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2;
                    v_a_7876_ = lean_array_uget_borrowed(v_as_7868_, v_i_7870_);
                    v___x_7877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___closed__0;
                    crate::leanh::lean_inc(v_a_7876_);
                    v___x_7878_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_a_7876_,
                        v___x_7873_,
                    );
                    v___x_7879_ = lean_string_append(v___x_7877_, v___x_7878_);
                    crate::leanh::lean_dec_ref(v___x_7878_);
                    v___x_7880_ = lean_string_append(v___x_7879_, v___x_7875_);
                    v___x_7881_ = lean_string_append(v_b_7871_, v___x_7880_);
                    crate::leanh::lean_dec_ref(v___x_7880_);
                    v___x_7882_ = 1usize;
                    v___x_7883_ = lean_usize_add(v_i_7870_, v___x_7882_);
                    v_i_7870_ = v___x_7883_;
                    v_b_7871_ = v___x_7881_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___boxed(
    mut v_as_7885_: *mut crate::leanh::LeanObject,
    mut v_sz_7886_: *mut crate::leanh::LeanObject,
    mut v_i_7887_: *mut crate::leanh::LeanObject,
    mut v_b_7888_: *mut crate::leanh::LeanObject,
    mut v___y_7889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7890_: usize = 0;
    let mut v_i_boxed_7891_: usize = 0;
    let mut v_res_7892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7890_ = crate::leanh::lean_unbox_usize(v_sz_7886_);
    crate::leanh::lean_dec(v_sz_7886_);
    v_i_boxed_7891_ = crate::leanh::lean_unbox_usize(v_i_7887_);
    crate::leanh::lean_dec(v_i_7887_);
    v_res_7892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v_as_7885_, v_sz_boxed_7890_, v_i_boxed_7891_, v_b_7888_);
    crate::leanh::lean_dec_ref(v_as_7885_);
    return v_res_7892_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0(
    mut v___x_7894_: u8,
    mut v_stx_7895_: *mut crate::leanh::LeanObject,
    mut v___x_7896_: u8,
    mut v___y_7897_: *mut crate::leanh::LeanObject,
    mut v___y_7898_: *mut crate::leanh::LeanObject,
    mut v___y_7899_: *mut crate::leanh::LeanObject,
    mut v___y_7900_: *mut crate::leanh::LeanObject,
    mut v___y_7901_: *mut crate::leanh::LeanObject,
    mut v___y_7902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_7905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7916_: u8 = 0;
    let mut v_cancelTk_x3f_7917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7918_: u8 = 0;
    let mut v_inheritedTraceOptions_7919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7923_: usize = 0;
    let mut v___x_7924_: usize = 0;
    let mut v___x_7925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7930_: u8 = 0;
    let mut v___x_7931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7942_: usize = 0;
    let mut v___x_7943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7947_: u8 = 0;
    let mut v___x_7948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7949_: u8 = 0;
    let mut v___x_7950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7957_: usize = 0;
    let mut v___x_7958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: u8 = 0;
    let mut v___x_7965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7970_: u8 = 0;
    let mut v___x_7972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7974_: u8 = 0;
    let mut v_a_7975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7978_: u8 = 0;
    let mut v___x_7980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7982_: u8 = 0;
    let mut v___x_7983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7987_: u8 = 0;
    let mut v_a_7988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7991_: u8 = 0;
    let mut v___x_7993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7995_: u8 = 0;
    let mut v___y_7997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8021_: u8 = 0;
    let mut v___x_8022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8033_: u8 = 0;
    let mut v___x_8034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8038_: u8 = 0;
    let mut v___x_8039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8040_: u8 = 0;
    let mut v_a_8041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8044_: u8 = 0;
    let mut v___x_8046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8048_: u8 = 0;
    let mut v___y_8050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8060_: u8 = 0;
    let mut v___x_8061_: u8 = 0;
    let mut v_m_x3f_8063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_x3f_8064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8080_: u8 = 0;
    let mut v_sz_8081_: usize = 0;
    let mut v___x_8082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8086_: u8 = 0;
    let mut v_a_8087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8090_: u8 = 0;
    let mut v___x_8092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8094_: u8 = 0;
    let mut v_a_8095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8098_: u8 = 0;
    let mut v___x_8100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8102_: u8 = 0;
    let mut v___x_8103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_x3f_8106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_x3f_8114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8119_: u8 = 0;
    let mut v___x_8120_: u8 = 0;
    let mut v___x_8121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8123_: u8 = 0;
    let mut v___x_8124_: u8 = 0;
    let mut v___x_8125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_x3f_8126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_7894_ == 0 {
                    crate::leanh::lean_dec(v_stx_7895_);
                    v___x_7904_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
                    return v___x_7904_;
                } else {
                    v_fileName_7905_ = crate::leanh::lean_ctor_get(v___y_7901_, 0);
                    v_fileMap_7906_ = crate::leanh::lean_ctor_get(v___y_7901_, 1);
                    v_options_7907_ = crate::leanh::lean_ctor_get(v___y_7901_, 2);
                    v_currRecDepth_7908_ = crate::leanh::lean_ctor_get(v___y_7901_, 3);
                    v_maxRecDepth_7909_ = crate::leanh::lean_ctor_get(v___y_7901_, 4);
                    v_ref_7910_ = crate::leanh::lean_ctor_get(v___y_7901_, 5);
                    v_currNamespace_7911_ = crate::leanh::lean_ctor_get(v___y_7901_, 6);
                    v_openDecls_7912_ = crate::leanh::lean_ctor_get(v___y_7901_, 7);
                    v_initHeartbeats_7913_ = crate::leanh::lean_ctor_get(v___y_7901_, 8);
                    v_quotContext_7914_ = crate::leanh::lean_ctor_get(v___y_7901_, 10);
                    v_currMacroScope_7915_ = crate::leanh::lean_ctor_get(v___y_7901_, 11);
                    v_diag_7916_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_7901_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_7917_ = crate::leanh::lean_ctor_get(v___y_7901_, 12);
                    v_suppressElabErrors_7918_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_7901_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_7919_ = crate::leanh::lean_ctor_get(v___y_7901_, 13);
                    v___x_7920_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_7921_ = l_Lean_Syntax_getArg(v_stx_7895_, v___x_7920_);
                    v___x_7922_ = l_Lean_Syntax_getArgs(v___x_7921_);
                    crate::leanh::lean_dec(v___x_7921_);
                    v_sz_7923_ = lean_array_size(v___x_7922_);
                    v___x_7924_ = 0usize;
                    v___x_7925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_7923_, v___x_7924_, v___x_7922_);
                    if crate::leanh::lean_obj_tag(v___x_7925_) == 0 {
                        crate::leanh::lean_dec(v_stx_7895_);
                        v___x_7926_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
                        return v___x_7926_;
                    } else {
                        v_val_7927_ = crate::leanh::lean_ctor_get(v___x_7925_, 0);
                        v_isSharedCheck_8130_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7925_)) as u8;
                        if v_isSharedCheck_8130_ == 0 {
                            v___x_7929_ = v___x_7925_;
                            v_isShared_7930_ = v_isSharedCheck_8130_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_7927_);
                            crate::leanh::lean_dec(v___x_7925_);
                            v___x_7929_ = crate::leanh::lean_box(0);
                            v_isShared_7930_ = v_isSharedCheck_8130_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7931_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_7919_);
                crate::leanh::lean_inc(v_cancelTk_x3f_7917_);
                crate::leanh::lean_inc(v_currMacroScope_7915_);
                crate::leanh::lean_inc(v_quotContext_7914_);
                crate::leanh::lean_inc(v_initHeartbeats_7913_);
                crate::leanh::lean_inc(v_openDecls_7912_);
                crate::leanh::lean_inc(v_currNamespace_7911_);
                crate::leanh::lean_inc(v_ref_7910_);
                crate::leanh::lean_inc(v_maxRecDepth_7909_);
                crate::leanh::lean_inc(v_currRecDepth_7908_);
                crate::leanh::lean_inc_ref(v_options_7907_);
                crate::leanh::lean_inc_ref(v_fileMap_7906_);
                crate::leanh::lean_inc_ref(v_fileName_7905_);
                v___x_8022_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_8022_, 0, v_fileName_7905_);
                crate::leanh::lean_ctor_set(v___x_8022_, 1, v_fileMap_7906_);
                crate::leanh::lean_ctor_set(v___x_8022_, 2, v_options_7907_);
                crate::leanh::lean_ctor_set(v___x_8022_, 3, v_currRecDepth_7908_);
                crate::leanh::lean_ctor_set(v___x_8022_, 4, v_maxRecDepth_7909_);
                crate::leanh::lean_ctor_set(v___x_8022_, 5, v_ref_7910_);
                crate::leanh::lean_ctor_set(v___x_8022_, 6, v_currNamespace_7911_);
                crate::leanh::lean_ctor_set(v___x_8022_, 7, v_openDecls_7912_);
                crate::leanh::lean_ctor_set(v___x_8022_, 8, v_initHeartbeats_7913_);
                crate::leanh::lean_ctor_set(v___x_8022_, 9, v___x_7931_);
                crate::leanh::lean_ctor_set(v___x_8022_, 10, v_quotContext_7914_);
                crate::leanh::lean_ctor_set(v___x_8022_, 11, v_currMacroScope_7915_);
                crate::leanh::lean_ctor_set(v___x_8022_, 12, v_cancelTk_x3f_7917_);
                crate::leanh::lean_ctor_set(v___x_8022_, 13, v_inheritedTraceOptions_7919_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_8022_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_7916_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_8022_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7918_,
                );
                v___x_8023_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_8103_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_8104_ = l_Lean_Syntax_getArg(v_stx_7895_, v___x_8103_);
                v___x_8119_ = l_Lean_Syntax_isNone(v___x_8104_);
                if v___x_8119_ == 0 {
                    crate::leanh::lean_inc(v___x_8104_);
                    v___x_8120_ = l_Lean_Syntax_matchesNull(v___x_8104_, v___x_8103_);
                    if v___x_8120_ == 0 {
                        crate::leanh::lean_dec(v___x_8104_);
                        crate::leanh::lean_dec_ref_known(v___x_8022_, 14);
                        crate::leanh::lean_del_object(v___x_7929_);
                        crate::leanh::lean_dec(v_val_7927_);
                        crate::leanh::lean_dec(v_stx_7895_);
                        v___x_8121_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
                        return v___x_8121_;
                    } else {
                        v___x_8122_ = l_Lean_Syntax_getArg(v___x_8104_, v___x_8023_);
                        v___x_8123_ = l_Lean_Syntax_isNone(v___x_8122_);
                        if v___x_8123_ == 0 {
                            crate::leanh::lean_inc(v___x_8122_);
                            v___x_8124_ = l_Lean_Syntax_matchesNull(v___x_8122_, v___x_8023_);
                            if v___x_8124_ == 0 {
                                crate::leanh::lean_dec(v___x_8122_);
                                crate::leanh::lean_dec(v___x_8104_);
                                crate::leanh::lean_dec_ref_known(v___x_8022_, 14);
                                crate::leanh::lean_del_object(v___x_7929_);
                                crate::leanh::lean_dec(v_val_7927_);
                                crate::leanh::lean_dec(v_stx_7895_);
                                v___x_8125_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
                                return v___x_8125_;
                            } else {
                                v_m_x3f_8126_ = l_Lean_Syntax_getArg(v___x_8122_, v___x_7931_);
                                crate::leanh::lean_dec(v___x_8122_);
                                v___x_8127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_8127_, 0, v_m_x3f_8126_);
                                v_m_x3f_8106_ = v___x_8127_;
                                v___y_8107_ = v___y_7897_;
                                v___y_8108_ = v___y_7898_;
                                v___y_8109_ = v___y_7899_;
                                v___y_8110_ = v___y_7900_;
                                v___y_8111_ = v___x_8022_;
                                v___y_8112_ = v___y_7902_;
                                state = 24;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_8122_);
                            v___x_8128_ = crate::leanh::lean_box(0);
                            v_m_x3f_8106_ = v___x_8128_;
                            v___y_8107_ = v___y_7897_;
                            v___y_8108_ = v___y_7898_;
                            v___y_8109_ = v___y_7899_;
                            v___y_8110_ = v___y_7900_;
                            v___y_8111_ = v___x_8022_;
                            v___y_8112_ = v___y_7902_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_8104_);
                    crate::leanh::lean_del_object(v___x_7929_);
                    v___x_8129_ = crate::leanh::lean_box(0);
                    v_m_x3f_8063_ = v___x_8129_;
                    v_ids_x3f_8064_ = v___x_8129_;
                    v___y_8065_ = v___y_7897_;
                    v___y_8066_ = v___y_7898_;
                    v___y_8067_ = v___y_7899_;
                    v___y_8068_ = v___y_7900_;
                    v___y_8069_ = v___x_8022_;
                    v___y_8070_ = v___y_7902_;
                    state = 17;
                    continue;
                }
            }
            2 => {
                v___x_7941_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0;
                v_sz_7942_ = lean_array_size(v___y_7940_);
                v___x_7943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(v___y_7939_, v___y_7940_, v_sz_7942_, v___x_7924_, v___x_7941_, v___y_7934_, v___y_7937_, v___y_7935_, v___y_7933_, v___y_7936_, v___y_7938_);
                crate::leanh::lean_dec_ref(v___y_7940_);
                if crate::leanh::lean_obj_tag(v___x_7943_) == 0 {
                    v_a_7944_ = crate::leanh::lean_ctor_get(v___x_7943_, 0);
                    v_isSharedCheck_7987_ = (!crate::leanh::lean_is_exclusive(v___x_7943_)) as u8;
                    if v_isSharedCheck_7987_ == 0 {
                        v___x_7946_ = v___x_7943_;
                        v_isShared_7947_ = v_isSharedCheck_7987_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7944_);
                        crate::leanh::lean_dec(v___x_7943_);
                        v___x_7946_ = crate::leanh::lean_box(0);
                        v_isShared_7947_ = v_isSharedCheck_7987_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_7936_);
                    crate::leanh::lean_dec(v_stx_7895_);
                    v_a_7988_ = crate::leanh::lean_ctor_get(v___x_7943_, 0);
                    v_isSharedCheck_7995_ = (!crate::leanh::lean_is_exclusive(v___x_7943_)) as u8;
                    if v_isSharedCheck_7995_ == 0 {
                        v___x_7990_ = v___x_7943_;
                        v_isShared_7991_ = v_isSharedCheck_7995_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7988_);
                        crate::leanh::lean_dec(v___x_7943_);
                        v___x_7990_ = crate::leanh::lean_box(0);
                        v_isShared_7991_ = v_isSharedCheck_7995_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7948_ = lean_array_get_size(v_a_7944_);
                v___x_7949_ = lean_nat_dec_eq(v___x_7948_, v___x_7931_);
                if v___x_7949_ == 0 {
                    crate::leanh::lean_del_object(v___x_7946_);
                    v___x_7950_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5;
                    crate::leanh::lean_inc(v_stx_7895_);
                    v___x_7951_ = l_Lean_PrettyPrinter_ppCategory(
                        v___x_7950_,
                        v_stx_7895_,
                        v___y_7936_,
                        v___y_7938_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7951_) == 0 {
                        v_a_7952_ = crate::leanh::lean_ctor_get(v___x_7951_, 0);
                        crate::leanh::lean_inc(v_a_7952_);
                        crate::leanh::lean_dec_ref_known(v___x_7951_, 1);
                        v___x_7953_ = l_Std_Format_defWidth;
                        v___x_7954_ =
                            l_Std_Format_pretty(v_a_7952_, v___x_7953_, v___x_7931_, v___x_7931_);
                        v___x_7955_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2;
                        v___x_7956_ = lean_string_append(v___x_7954_, v___x_7955_);
                        v_sz_7957_ = lean_array_size(v_a_7944_);
                        v___x_7958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v_a_7944_, v_sz_7957_, v___x_7924_, v___x_7956_);
                        crate::leanh::lean_dec(v_a_7944_);
                        if crate::leanh::lean_obj_tag(v___x_7958_) == 0 {
                            v_a_7959_ = crate::leanh::lean_ctor_get(v___x_7958_, 0);
                            crate::leanh::lean_inc(v_a_7959_);
                            crate::leanh::lean_dec_ref_known(v___x_7958_, 1);
                            v___x_7960_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7960_, 0, v_a_7959_);
                            v___x_7961_ = crate::leanh::lean_box(0);
                            v___x_7962_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7962_, 0, v___x_7960_);
                            crate::leanh::lean_ctor_set(v___x_7962_, 1, v___x_7961_);
                            crate::leanh::lean_ctor_set(v___x_7962_, 2, v___x_7961_);
                            crate::leanh::lean_ctor_set(v___x_7962_, 3, v___x_7961_);
                            crate::leanh::lean_ctor_set(v___x_7962_, 4, v___x_7961_);
                            crate::leanh::lean_ctor_set(v___x_7962_, 5, v___x_7961_);
                            v___x_7963_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___closed__0;
                            v___x_7964_ = 4;
                            v___x_7965_ = l_Lean_MessageData_nil;
                            v___x_7966_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                                v_stx_7895_,
                                v___x_7962_,
                                v___x_7961_,
                                v___x_7963_,
                                v___x_7961_,
                                v___x_7964_,
                                v___x_7965_,
                                v___y_7936_,
                                v___y_7938_,
                            );
                            crate::leanh::lean_dec_ref(v___y_7936_);
                            return v___x_7966_;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_7936_);
                            crate::leanh::lean_dec(v_stx_7895_);
                            v_a_7967_ = crate::leanh::lean_ctor_get(v___x_7958_, 0);
                            v_isSharedCheck_7974_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7958_)) as u8;
                            if v_isSharedCheck_7974_ == 0 {
                                v___x_7969_ = v___x_7958_;
                                v_isShared_7970_ = v_isSharedCheck_7974_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7967_);
                                crate::leanh::lean_dec(v___x_7958_);
                                v___x_7969_ = crate::leanh::lean_box(0);
                                v_isShared_7970_ = v_isSharedCheck_7974_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7944_);
                        crate::leanh::lean_dec_ref(v___y_7936_);
                        crate::leanh::lean_dec(v_stx_7895_);
                        v_a_7975_ = crate::leanh::lean_ctor_get(v___x_7951_, 0);
                        v_isSharedCheck_7982_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7951_)) as u8;
                        if v_isSharedCheck_7982_ == 0 {
                            v___x_7977_ = v___x_7951_;
                            v_isShared_7978_ = v_isSharedCheck_7982_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7975_);
                            crate::leanh::lean_dec(v___x_7951_);
                            v___x_7977_ = crate::leanh::lean_box(0);
                            v_isShared_7978_ = v_isSharedCheck_7982_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7944_);
                    crate::leanh::lean_dec_ref(v___y_7936_);
                    crate::leanh::lean_dec(v_stx_7895_);
                    v___x_7983_ = crate::leanh::lean_box(0);
                    if v_isShared_7947_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7946_, 0, v___x_7983_);
                        v___x_7985_ = v___x_7946_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7986_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7986_, 0, v___x_7983_);
                        v___x_7985_ = v_reuseFailAlloc_7986_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_7970_ == 0 {
                    v___x_7972_ = v___x_7969_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7973_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7973_, 0, v_a_7967_);
                    v___x_7972_ = v_reuseFailAlloc_7973_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7972_;
            }
            6 => {
                if v_isShared_7978_ == 0 {
                    v___x_7980_ = v___x_7977_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7981_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7981_, 0, v_a_7975_);
                    v___x_7980_ = v_reuseFailAlloc_7981_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7980_;
            }
            8 => {
                return v___x_7985_;
            }
            9 => {
                if v_isShared_7991_ == 0 {
                    v___x_7993_ = v___x_7990_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7994_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7994_, 0, v_a_7988_);
                    v___x_7993_ = v_reuseFailAlloc_7994_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7993_;
            }
            11 => {
                v___x_8008_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v___y_8003_, v___y_7999_, v___y_8006_, v___y_8007_);
                crate::leanh::lean_dec(v___y_8007_);
                crate::leanh::lean_dec(v___y_8003_);
                v___y_7933_ = v___y_7997_;
                v___y_7934_ = v___y_7998_;
                v___y_7935_ = v___y_8000_;
                v___y_7936_ = v___y_8001_;
                v___y_7937_ = v___y_8002_;
                v___y_7938_ = v___y_8005_;
                v___y_7939_ = v___y_8004_;
                v___y_7940_ = v___x_8008_;
                state = 2;
                continue;
            }
            12 => {
                v___x_8021_ = lean_nat_dec_le(v___y_8020_, v___y_8015_);
                if v___x_8021_ == 0 {
                    crate::leanh::lean_dec(v___y_8015_);
                    crate::leanh::lean_inc(v___y_8020_);
                    v___y_7997_ = v___y_8010_;
                    v___y_7998_ = v___y_8011_;
                    v___y_7999_ = v___y_8012_;
                    v___y_8000_ = v___y_8013_;
                    v___y_8001_ = v___y_8014_;
                    v___y_8002_ = v___y_8016_;
                    v___y_8003_ = v___y_8017_;
                    v___y_8004_ = v___y_8019_;
                    v___y_8005_ = v___y_8018_;
                    v___y_8006_ = v___y_8020_;
                    v___y_8007_ = v___y_8020_;
                    state = 11;
                    continue;
                } else {
                    v___y_7997_ = v___y_8010_;
                    v___y_7998_ = v___y_8011_;
                    v___y_7999_ = v___y_8012_;
                    v___y_8000_ = v___y_8013_;
                    v___y_8001_ = v___y_8014_;
                    v___y_8002_ = v___y_8016_;
                    v___y_8003_ = v___y_8017_;
                    v___y_8004_ = v___y_8019_;
                    v___y_8005_ = v___y_8018_;
                    v___y_8006_ = v___y_8020_;
                    v___y_8007_ = v___y_8015_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                v___x_8034_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v___y_8026_, v___y_8033_, v___y_8032_);
                crate::leanh::lean_dec(v___y_8026_);
                if crate::leanh::lean_obj_tag(v___x_8034_) == 0 {
                    v_a_8035_ = crate::leanh::lean_ctor_get(v___x_8034_, 0);
                    crate::leanh::lean_inc(v_a_8035_);
                    crate::leanh::lean_dec_ref_known(v___x_8034_, 1);
                    v___x_8036_ = lean_array_mk(v_a_8035_);
                    v___x_8037_ = lean_array_get_size(v___x_8036_);
                    v___x_8038_ = lean_nat_dec_eq(v___x_8037_, v___x_7931_);
                    if v___x_8038_ == 0 {
                        v___x_8039_ = lean_nat_sub(v___x_8037_, v___x_8023_);
                        v___x_8040_ = lean_nat_dec_le(v___x_7931_, v___x_8039_);
                        if v___x_8040_ == 0 {
                            crate::leanh::lean_inc(v___x_8039_);
                            v___y_8010_ = v___y_8025_;
                            v___y_8011_ = v___y_8027_;
                            v___y_8012_ = v___x_8036_;
                            v___y_8013_ = v___y_8028_;
                            v___y_8014_ = v___y_8029_;
                            v___y_8015_ = v___x_8039_;
                            v___y_8016_ = v___y_8030_;
                            v___y_8017_ = v___x_8037_;
                            v___y_8018_ = v___y_8032_;
                            v___y_8019_ = v___y_8031_;
                            v___y_8020_ = v___x_8039_;
                            state = 12;
                            continue;
                        } else {
                            v___y_8010_ = v___y_8025_;
                            v___y_8011_ = v___y_8027_;
                            v___y_8012_ = v___x_8036_;
                            v___y_8013_ = v___y_8028_;
                            v___y_8014_ = v___y_8029_;
                            v___y_8015_ = v___x_8039_;
                            v___y_8016_ = v___y_8030_;
                            v___y_8017_ = v___x_8037_;
                            v___y_8018_ = v___y_8032_;
                            v___y_8019_ = v___y_8031_;
                            v___y_8020_ = v___x_7931_;
                            state = 12;
                            continue;
                        }
                    } else {
                        v___y_7933_ = v___y_8025_;
                        v___y_7934_ = v___y_8027_;
                        v___y_7935_ = v___y_8028_;
                        v___y_7936_ = v___y_8029_;
                        v___y_7937_ = v___y_8030_;
                        v___y_7938_ = v___y_8032_;
                        v___y_7939_ = v___y_8031_;
                        v___y_7940_ = v___x_8036_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_8031_);
                    crate::leanh::lean_dec_ref(v___y_8029_);
                    crate::leanh::lean_dec(v_stx_7895_);
                    v_a_8041_ = crate::leanh::lean_ctor_get(v___x_8034_, 0);
                    v_isSharedCheck_8048_ = (!crate::leanh::lean_is_exclusive(v___x_8034_)) as u8;
                    if v_isSharedCheck_8048_ == 0 {
                        v___x_8043_ = v___x_8034_;
                        v_isShared_8044_ = v_isSharedCheck_8048_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8041_);
                        crate::leanh::lean_dec(v___x_8034_);
                        v___x_8043_ = crate::leanh::lean_box(0);
                        v_isShared_8044_ = v_isSharedCheck_8048_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_8044_ == 0 {
                    v___x_8046_ = v___x_8043_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_8047_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8047_, 0, v_a_8041_);
                    v___x_8046_ = v_reuseFailAlloc_8047_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_8046_;
            }
            16 => {
                if crate::leanh::lean_obj_tag(v___y_8050_) == 1 {
                    v_val_8059_ = crate::leanh::lean_ctor_get(v___y_8050_, 0);
                    crate::leanh::lean_inc(v_val_8059_);
                    crate::leanh::lean_dec_ref_known(v___y_8050_, 1);
                    if crate::leanh::lean_obj_tag(v_val_8059_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_val_8059_, 1);
                        v___y_8025_ = v___y_8051_;
                        v___y_8026_ = v___y_8058_;
                        v___y_8027_ = v___y_8052_;
                        v___y_8028_ = v___y_8053_;
                        v___y_8029_ = v___y_8054_;
                        v___y_8030_ = v___y_8055_;
                        v___y_8031_ = v___y_8057_;
                        v___y_8032_ = v___y_8056_;
                        v___y_8033_ = v___x_7896_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_val_8059_);
                        v___x_8060_ = 0;
                        v___y_8025_ = v___y_8051_;
                        v___y_8026_ = v___y_8058_;
                        v___y_8027_ = v___y_8052_;
                        v___y_8028_ = v___y_8053_;
                        v___y_8029_ = v___y_8054_;
                        v___y_8030_ = v___y_8055_;
                        v___y_8031_ = v___y_8057_;
                        v___y_8032_ = v___y_8056_;
                        v___y_8033_ = v___x_8060_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_8050_);
                    v___x_8061_ = 0;
                    v___y_8025_ = v___y_8051_;
                    v___y_8026_ = v___y_8058_;
                    v___y_8027_ = v___y_8052_;
                    v___y_8028_ = v___y_8053_;
                    v___y_8029_ = v___y_8054_;
                    v___y_8030_ = v___y_8055_;
                    v___y_8031_ = v___y_8057_;
                    v___y_8032_ = v___y_8056_;
                    v___y_8033_ = v___x_8061_;
                    state = 13;
                    continue;
                }
            }
            17 => {
                v___x_8071_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_val_7927_, v___y_8065_, v___y_8069_, v___y_8070_);
                if crate::leanh::lean_obj_tag(v___x_8071_) == 0 {
                    v_a_8072_ = crate::leanh::lean_ctor_get(v___x_8071_, 0);
                    crate::leanh::lean_inc(v_a_8072_);
                    crate::leanh::lean_dec_ref_known(v___x_8071_, 1);
                    v___x_8073_ =
                        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(
                            v_a_8072_,
                            v___y_8067_,
                            v___y_8068_,
                            v___y_8069_,
                            v___y_8070_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_8073_) == 0 {
                        if crate::leanh::lean_obj_tag(v_ids_x3f_8064_) == 0 {
                            v_a_8074_ = crate::leanh::lean_ctor_get(v___x_8073_, 0);
                            crate::leanh::lean_inc(v_a_8074_);
                            crate::leanh::lean_dec_ref_known(v___x_8073_, 1);
                            v___x_8075_ = crate::leanh::lean_box(0);
                            v___y_8050_ = v_m_x3f_8063_;
                            v___y_8051_ = v___y_8068_;
                            v___y_8052_ = v___y_8065_;
                            v___y_8053_ = v___y_8067_;
                            v___y_8054_ = v___y_8069_;
                            v___y_8055_ = v___y_8066_;
                            v___y_8056_ = v___y_8070_;
                            v___y_8057_ = v_a_8074_;
                            v___y_8058_ = v___x_8075_;
                            state = 16;
                            continue;
                        } else {
                            v_a_8076_ = crate::leanh::lean_ctor_get(v___x_8073_, 0);
                            crate::leanh::lean_inc(v_a_8076_);
                            crate::leanh::lean_dec_ref_known(v___x_8073_, 1);
                            v_val_8077_ = crate::leanh::lean_ctor_get(v_ids_x3f_8064_, 0);
                            v_isSharedCheck_8086_ =
                                (!crate::leanh::lean_is_exclusive(v_ids_x3f_8064_)) as u8;
                            if v_isSharedCheck_8086_ == 0 {
                                v___x_8079_ = v_ids_x3f_8064_;
                                v_isShared_8080_ = v_isSharedCheck_8086_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_8077_);
                                crate::leanh::lean_dec(v_ids_x3f_8064_);
                                v___x_8079_ = crate::leanh::lean_box(0);
                                v_isShared_8080_ = v_isSharedCheck_8086_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_8069_);
                        crate::leanh::lean_dec(v_ids_x3f_8064_);
                        crate::leanh::lean_dec(v_m_x3f_8063_);
                        crate::leanh::lean_dec(v_stx_7895_);
                        v_a_8087_ = crate::leanh::lean_ctor_get(v___x_8073_, 0);
                        v_isSharedCheck_8094_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8073_)) as u8;
                        if v_isSharedCheck_8094_ == 0 {
                            v___x_8089_ = v___x_8073_;
                            v_isShared_8090_ = v_isSharedCheck_8094_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8087_);
                            crate::leanh::lean_dec(v___x_8073_);
                            v___x_8089_ = crate::leanh::lean_box(0);
                            v_isShared_8090_ = v_isSharedCheck_8094_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_8069_);
                    crate::leanh::lean_dec(v_ids_x3f_8064_);
                    crate::leanh::lean_dec(v_m_x3f_8063_);
                    crate::leanh::lean_dec(v_stx_7895_);
                    v_a_8095_ = crate::leanh::lean_ctor_get(v___x_8071_, 0);
                    v_isSharedCheck_8102_ = (!crate::leanh::lean_is_exclusive(v___x_8071_)) as u8;
                    if v_isSharedCheck_8102_ == 0 {
                        v___x_8097_ = v___x_8071_;
                        v_isShared_8098_ = v_isSharedCheck_8102_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8095_);
                        crate::leanh::lean_dec(v___x_8071_);
                        v___x_8097_ = crate::leanh::lean_box(0);
                        v_isShared_8098_ = v_isSharedCheck_8102_;
                        state = 22;
                        continue;
                    }
                }
            }
            18 => {
                v_sz_8081_ = lean_array_size(v_val_8077_);
                v___x_8082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(v_sz_8081_, v___x_7924_, v_val_8077_);
                if v_isShared_8080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8079_, 0, v___x_8082_);
                    v___x_8084_ = v___x_8079_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_8085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8085_, 0, v___x_8082_);
                    v___x_8084_ = v_reuseFailAlloc_8085_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_8050_ = v_m_x3f_8063_;
                v___y_8051_ = v___y_8068_;
                v___y_8052_ = v___y_8065_;
                v___y_8053_ = v___y_8067_;
                v___y_8054_ = v___y_8069_;
                v___y_8055_ = v___y_8066_;
                v___y_8056_ = v___y_8070_;
                v___y_8057_ = v_a_8076_;
                v___y_8058_ = v___x_8084_;
                state = 16;
                continue;
            }
            20 => {
                if v_isShared_8090_ == 0 {
                    v___x_8092_ = v___x_8089_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_8093_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8093_, 0, v_a_8087_);
                    v___x_8092_ = v_reuseFailAlloc_8093_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_8092_;
            }
            22 => {
                if v_isShared_8098_ == 0 {
                    v___x_8100_ = v___x_8097_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_8101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8101_, 0, v_a_8095_);
                    v___x_8100_ = v_reuseFailAlloc_8101_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_8100_;
            }
            24 => {
                v___x_8113_ = l_Lean_Syntax_getArg(v___x_8104_, v___x_7920_);
                crate::leanh::lean_dec(v___x_8104_);
                v_ids_x3f_8114_ = l_Lean_Syntax_getArgs(v___x_8113_);
                crate::leanh::lean_dec(v___x_8113_);
                if v_isShared_7930_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7929_, 0, v_m_x3f_8106_);
                    v___x_8116_ = v___x_7929_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_8118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8118_, 0, v_m_x3f_8106_);
                    v___x_8116_ = v_reuseFailAlloc_8118_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_8117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8117_, 0, v_ids_x3f_8114_);
                v_m_x3f_8063_ = v___x_8116_;
                v_ids_x3f_8064_ = v___x_8117_;
                v___y_8065_ = v___y_8107_;
                v___y_8066_ = v___y_8108_;
                v___y_8067_ = v___y_8109_;
                v___y_8068_ = v___y_8110_;
                v___y_8069_ = v___y_8111_;
                v___y_8070_ = v___y_8112_;
                state = 17;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___boxed(
    mut v___x_8131_: *mut crate::leanh::LeanObject,
    mut v_stx_8132_: *mut crate::leanh::LeanObject,
    mut v___x_8133_: *mut crate::leanh::LeanObject,
    mut v___y_8134_: *mut crate::leanh::LeanObject,
    mut v___y_8135_: *mut crate::leanh::LeanObject,
    mut v___y_8136_: *mut crate::leanh::LeanObject,
    mut v___y_8137_: *mut crate::leanh::LeanObject,
    mut v___y_8138_: *mut crate::leanh::LeanObject,
    mut v___y_8139_: *mut crate::leanh::LeanObject,
    mut v___y_8140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11665__boxed_8141_: u8 = 0;
    let mut v___x_11666__boxed_8142_: u8 = 0;
    let mut v_res_8143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11665__boxed_8141_ = (crate::leanh::lean_unbox(v___x_8131_) as u8);
    v___x_11666__boxed_8142_ = (crate::leanh::lean_unbox(v___x_8133_) as u8);
    v_res_8143_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0(v___x_11665__boxed_8141_, v_stx_8132_, v___x_11666__boxed_8142_, v___y_8134_, v___y_8135_, v___y_8136_, v___y_8137_, v___y_8138_, v___y_8139_);
    crate::leanh::lean_dec(v___y_8139_);
    crate::leanh::lean_dec_ref(v___y_8138_);
    crate::leanh::lean_dec(v___y_8137_);
    crate::leanh::lean_dec_ref(v___y_8136_);
    crate::leanh::lean_dec(v___y_8135_);
    crate::leanh::lean_dec_ref(v___y_8134_);
    return v_res_8143_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck(
    mut v_stx_8149_: *mut crate::leanh::LeanObject,
    mut v_a_8150_: *mut crate::leanh::LeanObject,
    mut v_a_8151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8154_: u8 = 0;
    let mut v___x_8155_: u8 = 0;
    let mut v___x_8156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8153_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1;
    crate::leanh::lean_inc(v_stx_8149_);
    v___x_8154_ = l_Lean_Syntax_isOfKind(v_stx_8149_, v___x_8153_);
    v___x_8155_ = 1;
    v___x_8156_ = crate::leanh::lean_box((v___x_8154_) as usize);
    v___x_8157_ = crate::leanh::lean_box((v___x_8155_) as usize);
    v___f_8158_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
    crate::leanh::lean_closure_set(v___f_8158_, 0, v___x_8156_);
    crate::leanh::lean_closure_set(v___f_8158_, 1, v_stx_8149_);
    crate::leanh::lean_closure_set(v___f_8158_, 2, v___x_8157_);
    v___x_8159_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_8158_, v_a_8150_, v_a_8151_);
    return v___x_8159_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___boxed(
    mut v_stx_8160_: *mut crate::leanh::LeanObject,
    mut v_a_8161_: *mut crate::leanh::LeanObject,
    mut v_a_8162_: *mut crate::leanh::LeanObject,
    mut v_a_8163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8164_ =
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck(
            v_stx_8160_,
            v_a_8161_,
            v_a_8162_,
        );
    crate::leanh::lean_dec(v_a_8162_);
    crate::leanh::lean_dec_ref(v_a_8161_);
    return v_res_8164_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2(
    mut v_as_8165_: *mut crate::leanh::LeanObject,
    mut v_sz_8166_: usize,
    mut v_i_8167_: usize,
    mut v_b_8168_: *mut crate::leanh::LeanObject,
    mut v___y_8169_: *mut crate::leanh::LeanObject,
    mut v___y_8170_: *mut crate::leanh::LeanObject,
    mut v___y_8171_: *mut crate::leanh::LeanObject,
    mut v___y_8172_: *mut crate::leanh::LeanObject,
    mut v___y_8173_: *mut crate::leanh::LeanObject,
    mut v___y_8174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v_as_8165_, v_sz_8166_, v_i_8167_, v_b_8168_);
    return v___x_8176_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___boxed(
    mut v_as_8177_: *mut crate::leanh::LeanObject,
    mut v_sz_8178_: *mut crate::leanh::LeanObject,
    mut v_i_8179_: *mut crate::leanh::LeanObject,
    mut v_b_8180_: *mut crate::leanh::LeanObject,
    mut v___y_8181_: *mut crate::leanh::LeanObject,
    mut v___y_8182_: *mut crate::leanh::LeanObject,
    mut v___y_8183_: *mut crate::leanh::LeanObject,
    mut v___y_8184_: *mut crate::leanh::LeanObject,
    mut v___y_8185_: *mut crate::leanh::LeanObject,
    mut v___y_8186_: *mut crate::leanh::LeanObject,
    mut v___y_8187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_8188_: usize = 0;
    let mut v_i_boxed_8189_: usize = 0;
    let mut v_res_8190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8188_ = crate::leanh::lean_unbox_usize(v_sz_8178_);
    crate::leanh::lean_dec(v_sz_8178_);
    v_i_boxed_8189_ = crate::leanh::lean_unbox_usize(v_i_8179_);
    crate::leanh::lean_dec(v_i_8179_);
    v_res_8190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2(v_as_8177_, v_sz_boxed_8188_, v_i_boxed_8189_, v_b_8180_, v___y_8181_, v___y_8182_, v___y_8183_, v___y_8184_, v___y_8185_, v___y_8186_);
    crate::leanh::lean_dec(v___y_8186_);
    crate::leanh::lean_dec_ref(v___y_8185_);
    crate::leanh::lean_dec(v___y_8184_);
    crate::leanh::lean_dec_ref(v___y_8183_);
    crate::leanh::lean_dec(v___y_8182_);
    crate::leanh::lean_dec_ref(v___y_8181_);
    crate::leanh::lean_dec_ref(v_as_8177_);
    return v_res_8190_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3(
    mut v_n_8191_: *mut crate::leanh::LeanObject,
    mut v_as_8192_: *mut crate::leanh::LeanObject,
    mut v_lo_8193_: *mut crate::leanh::LeanObject,
    mut v_hi_8194_: *mut crate::leanh::LeanObject,
    mut v_w_8195_: *mut crate::leanh::LeanObject,
    mut v_hlo_8196_: *mut crate::leanh::LeanObject,
    mut v_hhi_8197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8198_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_8191_, v_as_8192_, v_lo_8193_, v_hi_8194_);
    return v___x_8198_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___boxed(
    mut v_n_8199_: *mut crate::leanh::LeanObject,
    mut v_as_8200_: *mut crate::leanh::LeanObject,
    mut v_lo_8201_: *mut crate::leanh::LeanObject,
    mut v_hi_8202_: *mut crate::leanh::LeanObject,
    mut v_w_8203_: *mut crate::leanh::LeanObject,
    mut v_hlo_8204_: *mut crate::leanh::LeanObject,
    mut v_hhi_8205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8206_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3(v_n_8199_, v_as_8200_, v_lo_8201_, v_hi_8202_, v_w_8203_, v_hlo_8204_, v_hhi_8205_);
    crate::leanh::lean_dec(v_hi_8202_);
    crate::leanh::lean_dec(v_n_8199_);
    return v_res_8206_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4(
    mut v_n_8207_: *mut crate::leanh::LeanObject,
    mut v_lo_8208_: *mut crate::leanh::LeanObject,
    mut v_hi_8209_: *mut crate::leanh::LeanObject,
    mut v_hhi_8210_: *mut crate::leanh::LeanObject,
    mut v_pivot_8211_: *mut crate::leanh::LeanObject,
    mut v_as_8212_: *mut crate::leanh::LeanObject,
    mut v_i_8213_: *mut crate::leanh::LeanObject,
    mut v_k_8214_: *mut crate::leanh::LeanObject,
    mut v_ilo_8215_: *mut crate::leanh::LeanObject,
    mut v_ik_8216_: *mut crate::leanh::LeanObject,
    mut v_w_8217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8218_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_8209_, v_pivot_8211_, v_as_8212_, v_i_8213_, v_k_8214_);
    return v___x_8218_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___boxed(
    mut v_n_8219_: *mut crate::leanh::LeanObject,
    mut v_lo_8220_: *mut crate::leanh::LeanObject,
    mut v_hi_8221_: *mut crate::leanh::LeanObject,
    mut v_hhi_8222_: *mut crate::leanh::LeanObject,
    mut v_pivot_8223_: *mut crate::leanh::LeanObject,
    mut v_as_8224_: *mut crate::leanh::LeanObject,
    mut v_i_8225_: *mut crate::leanh::LeanObject,
    mut v_k_8226_: *mut crate::leanh::LeanObject,
    mut v_ilo_8227_: *mut crate::leanh::LeanObject,
    mut v_ik_8228_: *mut crate::leanh::LeanObject,
    mut v_w_8229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8230_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4(v_n_8219_, v_lo_8220_, v_hi_8221_, v_hhi_8222_, v_pivot_8223_, v_as_8224_, v_i_8225_, v_k_8226_, v_ilo_8227_, v_ik_8228_, v_w_8229_);
    crate::leanh::lean_dec(v_pivot_8223_);
    crate::leanh::lean_dec(v_hi_8221_);
    crate::leanh::lean_dec(v_lo_8220_);
    crate::leanh::lean_dec(v_n_8219_);
    return v_res_8230_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1(
    mut v_ref_8231_: *mut crate::leanh::LeanObject,
    mut v_msgData_8232_: *mut crate::leanh::LeanObject,
    mut v_severity_8233_: u8,
    mut v_isSilent_8234_: u8,
    mut v___y_8235_: *mut crate::leanh::LeanObject,
    mut v___y_8236_: *mut crate::leanh::LeanObject,
    mut v___y_8237_: *mut crate::leanh::LeanObject,
    mut v___y_8238_: *mut crate::leanh::LeanObject,
    mut v___y_8239_: *mut crate::leanh::LeanObject,
    mut v___y_8240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8242_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_8231_, v_msgData_8232_, v_severity_8233_, v_isSilent_8234_, v___y_8237_, v___y_8238_, v___y_8239_, v___y_8240_);
    return v___x_8242_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___boxed(
    mut v_ref_8243_: *mut crate::leanh::LeanObject,
    mut v_msgData_8244_: *mut crate::leanh::LeanObject,
    mut v_severity_8245_: *mut crate::leanh::LeanObject,
    mut v_isSilent_8246_: *mut crate::leanh::LeanObject,
    mut v___y_8247_: *mut crate::leanh::LeanObject,
    mut v___y_8248_: *mut crate::leanh::LeanObject,
    mut v___y_8249_: *mut crate::leanh::LeanObject,
    mut v___y_8250_: *mut crate::leanh::LeanObject,
    mut v___y_8251_: *mut crate::leanh::LeanObject,
    mut v___y_8252_: *mut crate::leanh::LeanObject,
    mut v___y_8253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_8254_: u8 = 0;
    let mut v_isSilent_boxed_8255_: u8 = 0;
    let mut v_res_8256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_8254_ = (crate::leanh::lean_unbox(v_severity_8245_) as u8);
    v_isSilent_boxed_8255_ = (crate::leanh::lean_unbox(v_isSilent_8246_) as u8);
    v_res_8256_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1(v_ref_8243_, v_msgData_8244_, v_severity_boxed_8254_, v_isSilent_boxed_8255_, v___y_8247_, v___y_8248_, v___y_8249_, v___y_8250_, v___y_8251_, v___y_8252_);
    crate::leanh::lean_dec(v___y_8252_);
    crate::leanh::lean_dec_ref(v___y_8251_);
    crate::leanh::lean_dec(v___y_8250_);
    crate::leanh::lean_dec_ref(v___y_8249_);
    crate::leanh::lean_dec(v___y_8248_);
    crate::leanh::lean_dec_ref(v___y_8247_);
    crate::leanh::lean_dec(v_ref_8243_);
    return v_res_8256_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8262_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_8263_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1;
    v___x_8264_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__1;
    v___x_8265_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___boxed
            as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_8266_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_8262_,
        v___x_8263_,
        v___x_8264_,
        v___x_8265_,
    );
    return v___x_8266_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___boxed(
    mut v_a_8267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8268_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1();
    return v_res_8268_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_Lint(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Lint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt,
    );
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt,
    );
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt,
    );
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_Lint(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_Lint(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Lint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Lint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_Lint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_Lint(builtin);
}
