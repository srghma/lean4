// Lean compiler output
// Module: Lean.Elab.DeclModifiers
// Imports: Lean.DocString.Add Lean.Linter.Init Lean.Linter.EnvLinter.Nolint Lean.Parser.Command
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_length, lean_string_utf8_byte_size,
    lean_string_utf8_extract, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::Format::Basic::{
    l_Std_Format_defWidth, l_Std_Format_joinSep___redArg, l_Std_Format_pretty,
    l_Std_instToFormatFormat___lam__0___boxed,
};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_mapTR_loop___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Name_replacePrefix, l_Lean_Syntax_isNone};
use crate::r#gen::Init::Prelude::{
    l_Function_comp, l_Lean_MacroScopesView_review, l_Lean_Name_append, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getHeadInfo, l_Lean_Syntax_getId,
    l_Lean_Syntax_getKind, l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isIdent,
    l_Lean_Syntax_isOfKind, l_Lean_extractMacroScopes, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::KVMap::l_Lean_KVMap_instValueBool;
use crate::r#gen::Lean::Data::Name::{
    l_Lean_Name_isAnonymous, l_Lean_Name_isAtomic, l_Lean_Name_isPrefixOf,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{
    l_Lean_Option_get___redArg, l_Lean_Options_empty, lean_register_option,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DocString::Add::{
    initialize_Lean_DocString_Add, runtime_initialize_Lean_DocString_Add,
};
use crate::r#gen::Lean::DocString::Extension::l_Lean_doc_verso;
use crate::r#gen::Lean::Elab::Attributes::l_Lean_Elab_elabDeclAttrs___redArg;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_pushInfoLeaf___redArg;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_throwError___redArg, l_Lean_throwErrorAt___redArg, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::l_Lean_mkConst;
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Linter::EnvLinter::Nolint::{
    initialize_Lean_Linter_EnvLinter_Nolint, runtime_initialize_Lean_Linter_EnvLinter_Nolint,
};
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, l_Lean_Linter_logLintIf___redArg,
    runtime_initialize_Lean_Linter_Init,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Modifiers::{l_Lean_addProtected, l_Lean_mkPrivateName};
use crate::r#gen::Lean::MonadEnv::{
    l_Lean_mkConstWithLevelParams___redArg, l_Lean_withEnv___redArg,
};
use crate::r#gen::Lean::Parser::Command::{
    initialize_Lean_Parser_Command, runtime_initialize_Lean_Parser_Command,
};
use crate::r#gen::Lean::PrivateName::{
    l_Lean_isPrivateName, l_Lean_privateToUserName, lean_private_to_user_name,
};
use crate::r#gen::Lean::ResolveName::lean_is_reserved_name;
use crate::r#gen::Lean::Structure::{l_Lean_getStructureFieldsFlattened, l_Lean_isStructure};
pub static l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [114, 101, 100, 117, 110, 100, 97, 110, 116, 86, 105, 115, 105, 98, 105, 108, 105, 116, 121, 0]};
static mut l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject,5701751079888345786 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject,7254400451172284362 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value: leanh::LeanStringObject<58> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [119, 97, 114, 110, 32, 111, 110, 32, 114, 101, 100, 117, 110, 100, 97, 110, 116, 32, 96, 112, 114, 105, 118, 97, 116, 101, 96, 47, 96, 112, 117, 98, 108, 105, 99, 96, 32, 118, 105, 115, 105, 98, 105, 108, 105, 116, 121, 32, 109, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__3_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__0_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject,2225194685056464603 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__1_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject,15738509102271471615 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_linter_redundantVisibility: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        97, 32, 110, 111, 110, 45, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97,
        114, 97, 116, 105, 111, 110, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        96, 32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101, 101, 110, 32, 100,
        101, 99, 108, 97, 114, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__0_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        97, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105,
        111, 110, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__2_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        96, 32, 105, 115, 32, 97, 32, 114, 101, 115, 101, 114, 118, 101, 100, 32, 110, 97, 109,
        101, 0,
    ],
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__0_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110,
        32, 96, 0,
    ],
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedVisibility_default: u8 = 0;
pub static mut l_Lean_Elab_instInhabitedVisibility: u8 = 0;
pub static l_Lean_Elab_instToStringVisibility___lam__0___closed__0_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 101, 103, 117, 108, 97, 114, 0],
};
static mut l_Lean_Elab_instToStringVisibility___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToStringVisibility___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToStringVisibility___lam__0___closed__1_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [112, 114, 105, 118, 97, 116, 101, 0],
};
static mut l_Lean_Elab_instToStringVisibility___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToStringVisibility___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToStringVisibility___lam__0___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [112, 117, 98, 108, 105, 99, 0],
};
static mut l_Lean_Elab_instToStringVisibility___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToStringVisibility___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToStringVisibility___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instToStringVisibility___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToStringVisibility___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToStringVisibility___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instToStringVisibility: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToStringVisibility___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        59, 32, 116, 104, 101, 32, 109, 111, 100, 105, 102, 105, 101, 114, 32, 104, 97, 115, 32,
        110, 111, 32, 101, 102, 102, 101, 99, 116, 0,
    ],
};
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2_value:
    leanh::LeanStringObject<35> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        96, 112, 117, 98, 108, 105, 99, 96, 32, 105, 115, 32, 116, 104, 101, 32, 100, 101, 102, 97,
        117, 108, 116, 32, 118, 105, 115, 105, 98, 105, 108, 105, 116, 121, 0,
    ],
};
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        32, 105, 110, 115, 105, 100, 101, 32, 97, 32, 96, 112, 117, 98, 108, 105, 99, 32, 115, 101,
        99, 116, 105, 111, 110, 96, 0,
    ],
};
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7_value)
            as *mut leanh::LeanObject,
        17342580262104060118 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_instToStringVisibility___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
        10324751846086867157 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7_value)
            as *mut leanh::LeanObject,
        17342580262104060118 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_instToStringVisibility___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
        10411423847645546083 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10_value:
    leanh::LeanStringObject<31> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 118, 105, 115, 105, 98, 105, 108, 105,
        116, 121, 32, 109, 111, 100, 105, 102, 105, 101, 114, 0,
    ],
};
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12_value:
    leanh::LeanStringObject<115> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 115,
    m_capacity: 115,
    m_length: 114,
    m_data: [
        96, 112, 114, 105, 118, 97, 116, 101, 96, 32, 104, 97, 115, 32, 110, 111, 32, 101, 102,
        102, 101, 99, 116, 32, 105, 110, 32, 97, 32, 96, 109, 111, 100, 117, 108, 101, 96, 32, 102,
        105, 108, 101, 32, 111, 117, 116, 115, 105, 100, 101, 32, 96, 112, 117, 98, 108, 105, 99,
        32, 115, 101, 99, 116, 105, 111, 110, 96, 59, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105,
        111, 110, 115, 32, 97, 114, 101, 32, 97, 108, 114, 101, 97, 100, 121, 32, 96, 112, 114,
        105, 118, 97, 116, 101, 96, 32, 98, 121, 32, 100, 101, 102, 97, 117, 108, 116, 0,
    ],
};
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedRecKind_default: u8 = 0;
pub static mut l_Lean_Elab_instInhabitedRecKind: u8 = 0;
pub static mut l_Lean_Elab_instInhabitedComputeKind_default: u8 = 0;
pub static mut l_Lean_Elab_instInhabitedComputeKind: u8 = 0;
pub static l_Lean_Elab_instBEqComputeKind___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_instBEqComputeKind_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instBEqComputeKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instBEqComputeKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instBEqComputeKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instBEqComputeKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprComputeKind_repr___closed__0_value: leanh::LeanStringObject<
    30,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 67, 111, 109, 112, 117, 116, 101, 75, 105, 110,
        100, 46, 114, 101, 103, 117, 108, 97, 114, 0,
    ],
};
static mut l_Lean_Elab_instReprComputeKind_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprComputeKind_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprComputeKind_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_instReprComputeKind_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instReprComputeKind_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprComputeKind_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprComputeKind_repr___closed__2_value: leanh::LeanStringObject<
    27,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 67, 111, 109, 112, 117, 116, 101, 75, 105, 110,
        100, 46, 109, 101, 116, 97, 0,
    ],
};
static mut l_Lean_Elab_instReprComputeKind_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprComputeKind_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprComputeKind_repr___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_instReprComputeKind_repr___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instReprComputeKind_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprComputeKind_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprComputeKind_repr___closed__4_value: leanh::LeanStringObject<
    36,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 67, 111, 109, 112, 117, 116, 101, 75, 105, 110,
        100, 46, 110, 111, 110, 99, 111, 109, 112, 117, 116, 97, 98, 108, 101, 0,
    ],
};
static mut l_Lean_Elab_instReprComputeKind_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprComputeKind_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprComputeKind_repr___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_instReprComputeKind_repr___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instReprComputeKind_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprComputeKind_repr___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_instReprComputeKind_repr___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instReprComputeKind_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instReprComputeKind_repr___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instReprComputeKind_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_instReprComputeKind___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_instReprComputeKind_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instReprComputeKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprComputeKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instReprComputeKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprComputeKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedModifiers_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_instInhabitedModifiers_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedModifiers_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedModifiers_default___closed__1_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_instInhabitedModifiers_default___closed__0_value)
            as *mut leanh::LeanObject,
        33554432 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedModifiers_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedModifiers_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedModifiers_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedModifiers_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedModifiers: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedModifiers_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__0___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [64, 91, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__0___closed__1_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_instToFormatModifiers___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_instToFormatModifiers___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instToFormatModifiers___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instToFormatModifiers___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instToFormatModifiers___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_instToFormatModifiers___lam__0___closed__4_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__0___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__0___closed__6_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [108, 111, 99, 97, 108, 32, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__0___closed__7_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 99, 111, 112, 101, 100, 32, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__0___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [123, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__1_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__2_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__4_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [125, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__9_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [117, 110, 115, 97, 102, 101, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__10_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__11_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__10_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__12_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [112, 97, 114, 116, 105, 97, 108, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__13_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__14_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__13_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__15_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [110, 111, 110, 114, 101, 99, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__16_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__15_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__17_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__16_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__18_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [109, 101, 116, 97, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__19_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__18_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__20_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__19_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__21_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        110, 111, 110, 99, 111, 109, 112, 117, 116, 97, 98, 108, 101, 0,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__22_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__21_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__23_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__22_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__24_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [112, 114, 111, 116, 101, 99, 116, 101, 100, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__25_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__24_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__26_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__25_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__27_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToStringVisibility___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__28_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__27_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__29_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToStringVisibility___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__30_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__29_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__31_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [47, 45, 45, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__31_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__32_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__31_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__33_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__33_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__34_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [41, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__34_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__35_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__35: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__36_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__36: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__37_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__33_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__37: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__37_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__38_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__34_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__38: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__38_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__39_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 47, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__39: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__39_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__40_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__39_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__40: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__40_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__41_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__41: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__41_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___lam__1___closed__42_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Elab_instToFormatModifiers___lam__1___closed__42: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__42_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_instToFormatModifiers___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instToFormatModifiers___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_instToFormatFormat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instToFormatModifiers___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToFormatModifiers___closed__2_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_instToFormatModifiers___lam__1 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instToFormatModifiers___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instToFormatModifiers: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToStringModifiers___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_instToStringModifiers___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instToStringModifiers___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToStringModifiers___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instToStringModifiers___closed__1_value: leanh::LeanClosureObject<5> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Function_comp as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 5,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_instToStringModifiers___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instToStringModifiers___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToStringModifiers___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instToStringModifiers: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToStringModifiers___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 100, 111, 99, 32, 115, 116, 114, 105,
        110, 103, 0,
    ],
};
static mut l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7_value)
                as *mut leanh::LeanObject,
            17342580262104060118 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_elabModifiers___redArg___closed__0_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_elabModifiers___redArg___closed__0_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__12_value)
                as *mut leanh::LeanObject,
            14919950218492817255 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_elabModifiers___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabModifiers___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__5_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__6_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__7_value)
                as *mut leanh::LeanObject,
            17342580262104060118 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_elabModifiers___redArg___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_elabModifiers___redArg___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__18_value)
                as *mut leanh::LeanObject,
            4787239732180154236 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_elabModifiers___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabModifiers___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110,
        32, 110, 97, 109, 101, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        96, 44, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [96, 32, 104, 97, 115, 32, 102, 105, 101, 108, 100, 32, 96, 0],
};
static mut l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0_value:
    leanh::LeanStringObject<46> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        112, 114, 111, 116, 101, 99, 116, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105,
        111, 110, 115, 32, 109, 117, 115, 116, 32, 98, 101, 32, 105, 110, 32, 97, 32, 110, 97, 109,
        101, 115, 112, 97, 99, 101, 0,
    ],
};
static mut l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkDeclName___redArg___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [95, 114, 111, 111, 116, 95, 0],
    };
static mut l_Lean_Elab_mkDeclName___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkDeclName___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_mkDeclName___redArg___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkDeclName___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            626731335300788152 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_mkDeclName___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkDeclName___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_mkDeclName___redArg___closed__2_value: leanh::LeanStringObject<94> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 94,
        m_capacity: 94,
        m_length: 93,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
            110, 32, 110, 97, 109, 101, 32, 96, 95, 114, 111, 111, 116, 95, 96, 44, 32, 96, 95,
            114, 111, 111, 116, 95, 96, 32, 105, 115, 32, 97, 32, 112, 114, 101, 102, 105, 120, 32,
            117, 115, 101, 100, 32, 116, 111, 32, 114, 101, 102, 101, 114, 32, 116, 111, 32, 116,
            104, 101, 32, 39, 114, 111, 111, 116, 39, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101,
            0,
        ],
    };
static mut l_Lean_Elab_mkDeclName___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkDeclName___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_mkDeclName___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkDeclName___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_expandDeclIdCore___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_expandDeclIdCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandDeclIdCore___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_expandDeclIdCore___closed__1_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Elab_expandDeclIdCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandDeclIdCore___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_expandDeclIdCore___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_expandDeclIdCore___closed__1_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_expandDeclIdCore___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandDeclIdCore___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_expandDeclIdCore___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_expandDeclIdCore___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_expandDeclIdCore___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_expandDeclIdCore___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandDeclIdCore___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [97, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 32, 110, 97, 109, 101, 100, 32, 96, 0]};
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        10099171310552725070 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__7_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__4_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__5_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__8_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__6_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__1
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11_value
) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0(
    mut v_name_3790_: *mut leanh::LeanObject,
    mut v_decl_3791_: *mut leanh::LeanObject,
    mut v_ref_3792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: u8 = 0;
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3803_: u8 = 0;
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3808_: u8 = 0;
    let mut v_unused_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3813_: u8 = 0;
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3794_ = leanh::lean_ctor_get(v_decl_3791_, 0);
                v_descr_3795_ = leanh::lean_ctor_get(v_decl_3791_, 1);
                v_deprecation_x3f_3796_ = leanh::lean_ctor_get(v_decl_3791_, 2);
                v___x_3797_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3798_ = (leanh::lean_unbox(v_defValue_3794_) as u8);
                leanh::lean_ctor_set_uint8(v___x_3797_, 0 as u32, v___x_3798_);
                leanh::lean_inc(v_deprecation_x3f_3796_);
                leanh::lean_inc_ref(v_descr_3795_);
                leanh::lean_inc_n(v_name_3790_, 2);
                v___x_3799_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_3799_, 0, v_name_3790_);
                leanh::lean_ctor_set(v___x_3799_, 1, v_ref_3792_);
                leanh::lean_ctor_set(v___x_3799_, 2, v___x_3797_);
                leanh::lean_ctor_set(v___x_3799_, 3, v_descr_3795_);
                leanh::lean_ctor_set(v___x_3799_, 4, v_deprecation_x3f_3796_);
                v___x_3800_ = lean_register_option(v_name_3790_, v___x_3799_);
                if leanh::lean_obj_tag(v___x_3800_) == 0 {
                    v_isSharedCheck_3808_ = (!leanh::lean_is_exclusive(v___x_3800_)) as u8;
                    if v_isSharedCheck_3808_ == 0 {
                        v_unused_3809_ = leanh::lean_ctor_get(v___x_3800_, 0);
                        leanh::lean_dec(v_unused_3809_);
                        v___x_3802_ = v___x_3800_;
                        v_isShared_3803_ = v_isSharedCheck_3808_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3800_);
                        v___x_3802_ = leanh::lean_box(0);
                        v_isShared_3803_ = v_isSharedCheck_3808_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_3790_);
                    v_a_3810_ = leanh::lean_ctor_get(v___x_3800_, 0);
                    v_isSharedCheck_3817_ = (!leanh::lean_is_exclusive(v___x_3800_)) as u8;
                    if v_isSharedCheck_3817_ == 0 {
                        v___x_3812_ = v___x_3800_;
                        v_isShared_3813_ = v_isSharedCheck_3817_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3810_);
                        leanh::lean_dec(v___x_3800_);
                        v___x_3812_ = leanh::lean_box(0);
                        v_isShared_3813_ = v_isSharedCheck_3817_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_3794_);
                v___x_3804_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3804_, 0, v_name_3790_);
                leanh::lean_ctor_set(v___x_3804_, 1, v_defValue_3794_);
                if v_isShared_3803_ == 0 {
                    leanh::lean_ctor_set(v___x_3802_, 0, v___x_3804_);
                    v___x_3806_ = v___x_3802_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3807_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
                    v___x_3806_ = v_reuseFailAlloc_3807_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3806_;
            }
            3 => {
                if v_isShared_3813_ == 0 {
                    v___x_3815_ = v___x_3812_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
                    v___x_3815_ = v_reuseFailAlloc_3816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_3818_: *mut leanh::LeanObject,
    mut v_decl_3819_: *mut leanh::LeanObject,
    mut v_ref_3820_: *mut leanh::LeanObject,
    mut v_a_3821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3822_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0(v_name_3818_, v_decl_3819_, v_ref_3820_);
    leanh::lean_dec_ref(v_decl_3819_);
    return v_res_3822_;
}
pub unsafe fn l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3840_ = l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__2_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_;
    v___x_3841_ = l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__4_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_;
    v___x_3842_ = l___private_Lean_Elab_DeclModifiers_0__Lean_initFn___closed__6_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_;
    v___x_3843_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4__spec__0(v___x_3840_, v___x_3841_, v___x_3842_);
    return v___x_3843_;
}
pub unsafe fn l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4____boxed(
    mut v_a_3844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3845_ = l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_();
    return v_res_3845_;
}
pub unsafe fn _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3846_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3846_;
}
pub unsafe fn _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3847_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0_once
        ),
        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__0,
    );
    v___x_3848_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3848_, 0, v___x_3847_);
    return v___x_3848_;
}
pub unsafe fn _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3849_ = leanh::lean_unsigned_to_nat(32);
    v___x_3850_ = lean_mk_empty_array_with_capacity(v___x_3849_);
    v___x_3851_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3851_, 0, v___x_3850_);
    return v___x_3851_;
}
pub unsafe fn _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3852_: usize = 0;
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3852_ = 5usize;
    v___x_3853_ = leanh::lean_unsigned_to_nat(0);
    v___x_3854_ = leanh::lean_unsigned_to_nat(32);
    v___x_3855_ = lean_mk_empty_array_with_capacity(v___x_3854_);
    v___x_3856_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2_once
        ),
        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__2,
    );
    v___x_3857_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3857_, 0, v___x_3856_);
    leanh::lean_ctor_set(v___x_3857_, 1, v___x_3855_);
    leanh::lean_ctor_set(v___x_3857_, 2, v___x_3853_);
    leanh::lean_ctor_set(v___x_3857_, 3, v___x_3853_);
    leanh::lean_ctor_set_usize(v___x_3857_, 4, v___x_3852_);
    return v___x_3857_;
}
pub unsafe fn _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3858_ = leanh::lean_box(1);
    v___x_3859_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once
        ),
        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3,
    );
    v___x_3860_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__1,
    );
    v___x_3861_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3861_, 0, v___x_3860_);
    leanh::lean_ctor_set(v___x_3861_, 1, v___x_3859_);
    leanh::lean_ctor_set(v___x_3861_, 2, v___x_3858_);
    return v___x_3861_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(
    mut v_____do__lift_3862_: *mut leanh::LeanObject,
    mut v___x_3863_: u8,
    mut v_inst_3864_: *mut leanh::LeanObject,
    mut v_inst_3865_: *mut leanh::LeanObject,
    mut v_____do__lift_3866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3867_ = leanh::lean_box(0);
    v___x_3868_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3868_, 0, v___x_3867_);
    leanh::lean_ctor_set(v___x_3868_, 1, v_____do__lift_3862_);
    v___x_3869_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once
        ),
        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4,
    );
    v___x_3870_ = leanh::lean_box(0);
    v___x_3871_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
    leanh::lean_ctor_set(v___x_3871_, 0, v___x_3868_);
    leanh::lean_ctor_set(v___x_3871_, 1, v___x_3869_);
    leanh::lean_ctor_set(v___x_3871_, 2, v___x_3870_);
    leanh::lean_ctor_set(v___x_3871_, 3, v_____do__lift_3866_);
    leanh::lean_ctor_set_uint8(
        v___x_3871_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        v___x_3863_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3871_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
        v___x_3863_,
    );
    v___x_3872_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3872_, 0, v___x_3871_);
    v___x_3873_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_3864_, v_inst_3865_, v___x_3872_);
    return v___x_3873_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___boxed(
    mut v_____do__lift_3874_: *mut leanh::LeanObject,
    mut v___x_3875_: *mut leanh::LeanObject,
    mut v_inst_3876_: *mut leanh::LeanObject,
    mut v_inst_3877_: *mut leanh::LeanObject,
    mut v_____do__lift_3878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_880__boxed_3879_: u8 = 0;
    let mut v_res_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_880__boxed_3879_ = (leanh::lean_unbox(v___x_3875_) as u8);
    v_res_3880_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0(
        v_____do__lift_3874_,
        v___x_880__boxed_3879_,
        v_inst_3876_,
        v_inst_3877_,
        v_____do__lift_3878_,
    );
    return v_res_3880_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(
    mut v___x_3881_: u8,
    mut v_inst_3882_: *mut leanh::LeanObject,
    mut v_inst_3883_: *mut leanh::LeanObject,
    mut v_inst_3884_: *mut leanh::LeanObject,
    mut v_inst_3885_: *mut leanh::LeanObject,
    mut v_declName_3886_: *mut leanh::LeanObject,
    mut v_toBind_3887_: *mut leanh::LeanObject,
    mut v_____do__lift_3888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3889_ = leanh::lean_box((v___x_3881_) as usize);
    leanh::lean_inc_ref(v_inst_3882_);
    v___f_3890_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_3890_, 0, v_____do__lift_3888_);
    leanh::lean_closure_set(v___f_3890_, 1, v___x_3889_);
    leanh::lean_closure_set(v___f_3890_, 2, v_inst_3882_);
    leanh::lean_closure_set(v___f_3890_, 3, v_inst_3883_);
    v___x_3891_ = l_Lean_mkConstWithLevelParams___redArg(
        v_inst_3882_,
        v_inst_3884_,
        v_inst_3885_,
        v_declName_3886_,
    );
    v___x_3892_ = leanh::lean_apply_4(
        v_toBind_3887_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3891_,
        v___f_3890_,
    );
    return v___x_3892_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1___boxed(
    mut v___x_3893_: *mut leanh::LeanObject,
    mut v_inst_3894_: *mut leanh::LeanObject,
    mut v_inst_3895_: *mut leanh::LeanObject,
    mut v_inst_3896_: *mut leanh::LeanObject,
    mut v_inst_3897_: *mut leanh::LeanObject,
    mut v_declName_3898_: *mut leanh::LeanObject,
    mut v_toBind_3899_: *mut leanh::LeanObject,
    mut v_____do__lift_3900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_924__boxed_3901_: u8 = 0;
    let mut v_res_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_924__boxed_3901_ = (leanh::lean_unbox(v___x_3893_) as u8);
    v_res_3902_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1(
        v___x_924__boxed_3901_,
        v_inst_3894_,
        v_inst_3895_,
        v_inst_3896_,
        v_inst_3897_,
        v_declName_3898_,
        v_toBind_3899_,
        v_____do__lift_3900_,
    );
    return v_res_3902_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(
    mut v_toMonadRef_3903_: *mut leanh::LeanObject,
    mut v___x_3904_: u8,
    mut v_inst_3905_: *mut leanh::LeanObject,
    mut v_inst_3906_: *mut leanh::LeanObject,
    mut v_inst_3907_: *mut leanh::LeanObject,
    mut v_inst_3908_: *mut leanh::LeanObject,
    mut v_toBind_3909_: *mut leanh::LeanObject,
    mut v_declName_3910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRef_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getRef_3911_ = leanh::lean_ctor_get(v_toMonadRef_3903_, 0);
    leanh::lean_inc(v_getRef_3911_);
    leanh::lean_dec_ref(v_toMonadRef_3903_);
    v___x_3912_ = leanh::lean_box((v___x_3904_) as usize);
    leanh::lean_inc(v_toBind_3909_);
    v___f_3913_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_3913_, 0, v___x_3912_);
    leanh::lean_closure_set(v___f_3913_, 1, v_inst_3905_);
    leanh::lean_closure_set(v___f_3913_, 2, v_inst_3906_);
    leanh::lean_closure_set(v___f_3913_, 3, v_inst_3907_);
    leanh::lean_closure_set(v___f_3913_, 4, v_inst_3908_);
    leanh::lean_closure_set(v___f_3913_, 5, v_declName_3910_);
    leanh::lean_closure_set(v___f_3913_, 6, v_toBind_3909_);
    v___x_3914_ = leanh::lean_apply_4(
        v_toBind_3909_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRef_3911_,
        v___f_3913_,
    );
    return v___x_3914_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed(
    mut v_toMonadRef_3915_: *mut leanh::LeanObject,
    mut v___x_3916_: *mut leanh::LeanObject,
    mut v_inst_3917_: *mut leanh::LeanObject,
    mut v_inst_3918_: *mut leanh::LeanObject,
    mut v_inst_3919_: *mut leanh::LeanObject,
    mut v_inst_3920_: *mut leanh::LeanObject,
    mut v_toBind_3921_: *mut leanh::LeanObject,
    mut v_declName_3922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_950__boxed_3923_: u8 = 0;
    let mut v_res_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_950__boxed_3923_ = (leanh::lean_unbox(v___x_3916_) as u8);
    v_res_3924_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(
        v_toMonadRef_3915_,
        v___x_950__boxed_3923_,
        v_inst_3917_,
        v_inst_3918_,
        v_inst_3919_,
        v_inst_3920_,
        v_toBind_3921_,
        v_declName_3922_,
    );
    return v_res_3924_;
}
pub unsafe fn _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3926_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__0;
    v___x_3927_ = l_Lean_stringToMessageData(v___x_3926_);
    return v___x_3927_;
}
pub unsafe fn _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3929_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__2;
    v___x_3930_ = l_Lean_stringToMessageData(v___x_3929_);
    return v___x_3930_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(
    mut v_val_3931_: *mut leanh::LeanObject,
    mut v___x_3932_: u8,
    mut v_inst_3933_: *mut leanh::LeanObject,
    mut v_inst_3934_: *mut leanh::LeanObject,
    mut v_____r_3935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3936_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once
        ),
        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1,
    );
    v___x_3937_ = l_Lean_MessageData_ofConstName(v_val_3931_, v___x_3932_);
    v___x_3938_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3938_, 0, v___x_3936_);
    leanh::lean_ctor_set(v___x_3938_, 1, v___x_3937_);
    v___x_3939_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once
        ),
        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3,
    );
    v___x_3940_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3940_, 0, v___x_3938_);
    leanh::lean_ctor_set(v___x_3940_, 1, v___x_3939_);
    v___x_3941_ = l_Lean_throwError___redArg(v_inst_3933_, v_inst_3934_, v___x_3940_);
    return v___x_3941_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___boxed(
    mut v_val_3942_: *mut leanh::LeanObject,
    mut v___x_3943_: *mut leanh::LeanObject,
    mut v_inst_3944_: *mut leanh::LeanObject,
    mut v_inst_3945_: *mut leanh::LeanObject,
    mut v_____r_3946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_984__boxed_3947_: u8 = 0;
    let mut v_res_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_984__boxed_3947_ = (leanh::lean_unbox(v___x_3943_) as u8);
    v_res_3948_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3(
        v_val_3942_,
        v___x_984__boxed_3947_,
        v_inst_3944_,
        v_inst_3945_,
        v_____r_3946_,
    );
    return v_res_3948_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4(
    mut v_declName_3949_: *mut leanh::LeanObject,
    mut v_toPure_3950_: *mut leanh::LeanObject,
    mut v_env_3951_: *mut leanh::LeanObject,
    mut v_inst_3952_: *mut leanh::LeanObject,
    mut v_inst_3953_: *mut leanh::LeanObject,
    mut v_addInfo_3954_: *mut leanh::LeanObject,
    mut v_toBind_3955_: *mut leanh::LeanObject,
    mut v_____r_3956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3957_ = lean_private_to_user_name(v_declName_3949_);
    if leanh::lean_obj_tag(v___x_3957_) == 0 {
        let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toBind_3955_);
        leanh::lean_dec(v_addInfo_3954_);
        leanh::lean_dec_ref(v_inst_3953_);
        leanh::lean_dec_ref(v_inst_3952_);
        leanh::lean_dec_ref(v_env_3951_);
        v___x_3958_ = leanh::lean_box(0);
        v___x_3959_ =
            leanh::lean_apply_2(v_toPure_3950_, leanh::lean_box(0), v___x_3958_);
        return v___x_3959_;
    } else {
        let mut v_val_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3961_: u8 = 0;
        let mut v___x_3962_: u8 = 0;
        v_val_3960_ = leanh::lean_ctor_get(v___x_3957_, 0);
        leanh::lean_inc_n(v_val_3960_, 2);
        leanh::lean_dec_ref_known(v___x_3957_, 1);
        v___x_3961_ = 1;
        v___x_3962_ = l_Lean_Environment_contains(v_env_3951_, v_val_3960_, v___x_3961_);
        if v___x_3962_ == 0 {
            let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_3960_);
            leanh::lean_dec(v_toBind_3955_);
            leanh::lean_dec(v_addInfo_3954_);
            leanh::lean_dec_ref(v_inst_3953_);
            leanh::lean_dec_ref(v_inst_3952_);
            v___x_3963_ = leanh::lean_box(0);
            v___x_3964_ =
                leanh::lean_apply_2(v_toPure_3950_, leanh::lean_box(0), v___x_3963_);
            return v___x_3964_;
        } else {
            let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toPure_3950_);
            v___x_3965_ = leanh::lean_box((v___x_3961_) as usize);
            leanh::lean_inc(v_val_3960_);
            v___f_3966_ = leanh::lean_alloc_closure(
                l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___boxed
                    as *mut core::ffi::c_void,
                5,
                4,
            );
            leanh::lean_closure_set(v___f_3966_, 0, v_val_3960_);
            leanh::lean_closure_set(v___f_3966_, 1, v___x_3965_);
            leanh::lean_closure_set(v___f_3966_, 2, v_inst_3952_);
            leanh::lean_closure_set(v___f_3966_, 3, v_inst_3953_);
            v___x_3967_ = leanh::lean_apply_1(v_addInfo_3954_, v_val_3960_);
            v___x_3968_ = leanh::lean_apply_4(
                v_toBind_3955_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3967_,
                v___f_3966_,
            );
            return v___x_3968_;
        }
    }
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5(
    mut v___f_3969_: *mut leanh::LeanObject,
    mut v_____r_3970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3971_ = leanh::lean_apply_1(v___f_3969_, v_____r_3970_);
    return v___x_3971_;
}
pub unsafe fn _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3973_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__0;
    v___x_3974_ = l_Lean_stringToMessageData(v___x_3973_);
    return v___x_3974_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(
    mut v_declName_3975_: *mut leanh::LeanObject,
    mut v___x_3976_: u8,
    mut v_inst_3977_: *mut leanh::LeanObject,
    mut v_inst_3978_: *mut leanh::LeanObject,
    mut v_toBind_3979_: *mut leanh::LeanObject,
    mut v___f_3980_: *mut leanh::LeanObject,
    mut v_____r_3981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3982_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once
        ),
        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1,
    );
    v___x_3983_ = l_Lean_MessageData_ofConstName(v_declName_3975_, v___x_3976_);
    v___x_3984_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3984_, 0, v___x_3982_);
    leanh::lean_ctor_set(v___x_3984_, 1, v___x_3983_);
    v___x_3985_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once
        ),
        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3,
    );
    v___x_3986_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3986_, 0, v___x_3984_);
    leanh::lean_ctor_set(v___x_3986_, 1, v___x_3985_);
    v___x_3987_ = l_Lean_throwError___redArg(v_inst_3977_, v_inst_3978_, v___x_3986_);
    v___x_3988_ = leanh::lean_apply_4(
        v_toBind_3979_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3987_,
        v___f_3980_,
    );
    return v___x_3988_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___boxed(
    mut v_declName_3989_: *mut leanh::LeanObject,
    mut v___x_3990_: *mut leanh::LeanObject,
    mut v_inst_3991_: *mut leanh::LeanObject,
    mut v_inst_3992_: *mut leanh::LeanObject,
    mut v_toBind_3993_: *mut leanh::LeanObject,
    mut v___f_3994_: *mut leanh::LeanObject,
    mut v_____r_3995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1061__boxed_3996_: u8 = 0;
    let mut v_res_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1061__boxed_3996_ = (leanh::lean_unbox(v___x_3990_) as u8);
    v_res_3997_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6(
        v_declName_3989_,
        v___x_1061__boxed_3996_,
        v_inst_3991_,
        v_inst_3992_,
        v_toBind_3993_,
        v___f_3994_,
        v_____r_3995_,
    );
    return v_res_3997_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7(
    mut v_env_3998_: *mut leanh::LeanObject,
    mut v_declName_3999_: *mut leanh::LeanObject,
    mut v___f_4000_: *mut leanh::LeanObject,
    mut v_inst_4001_: *mut leanh::LeanObject,
    mut v_inst_4002_: *mut leanh::LeanObject,
    mut v_toBind_4003_: *mut leanh::LeanObject,
    mut v___f_4004_: *mut leanh::LeanObject,
    mut v_addInfo_4005_: *mut leanh::LeanObject,
    mut v_____r_4006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: u8 = 0;
    let mut v___x_4009_: u8 = 0;
    leanh::lean_inc(v_declName_3999_);
    v___x_4007_ = l_Lean_mkPrivateName(v_env_3998_, v_declName_3999_);
    v___x_4008_ = 1;
    leanh::lean_inc(v___x_4007_);
    v___x_4009_ = l_Lean_Environment_contains(v_env_3998_, v___x_4007_, v___x_4008_);
    if v___x_4009_ == 0 {
        let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_4007_);
        leanh::lean_dec(v_addInfo_4005_);
        leanh::lean_dec(v___f_4004_);
        leanh::lean_dec(v_toBind_4003_);
        leanh::lean_dec_ref(v_inst_4002_);
        leanh::lean_dec_ref(v_inst_4001_);
        leanh::lean_dec(v_declName_3999_);
        v___x_4010_ = leanh::lean_box(0);
        v___x_4011_ = leanh::lean_apply_1(v___f_4000_, v___x_4010_);
        return v___x_4011_;
    } else {
        let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_4000_);
        v___x_4012_ = leanh::lean_box((v___x_4008_) as usize);
        leanh::lean_inc(v_toBind_4003_);
        v___f_4013_ = leanh::lean_alloc_closure(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___boxed as *mut core::ffi::c_void,
            7,
            6,
        );
        leanh::lean_closure_set(v___f_4013_, 0, v_declName_3999_);
        leanh::lean_closure_set(v___f_4013_, 1, v___x_4012_);
        leanh::lean_closure_set(v___f_4013_, 2, v_inst_4001_);
        leanh::lean_closure_set(v___f_4013_, 3, v_inst_4002_);
        leanh::lean_closure_set(v___f_4013_, 4, v_toBind_4003_);
        leanh::lean_closure_set(v___f_4013_, 5, v___f_4004_);
        v___x_4014_ = leanh::lean_apply_1(v_addInfo_4005_, v___x_4007_);
        v___x_4015_ = leanh::lean_apply_4(
            v_toBind_4003_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4014_,
            v___f_4013_,
        );
        return v___x_4015_;
    }
}
pub unsafe fn _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4017_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__0;
    v___x_4018_ = l_Lean_stringToMessageData(v___x_4017_);
    return v___x_4018_;
}
pub unsafe fn _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4020_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__2;
    v___x_4021_ = l_Lean_stringToMessageData(v___x_4020_);
    return v___x_4021_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(
    mut v___f_4022_: *mut leanh::LeanObject,
    mut v_declName_4023_: *mut leanh::LeanObject,
    mut v___x_4024_: u8,
    mut v_inst_4025_: *mut leanh::LeanObject,
    mut v_inst_4026_: *mut leanh::LeanObject,
    mut v_toBind_4027_: *mut leanh::LeanObject,
    mut v___f_4028_: *mut leanh::LeanObject,
    mut v_env_4029_: *mut leanh::LeanObject,
    mut v_____do__lift_4030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4032_: u8 = 0;
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: u8 = 0;
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_4023_);
                v___x_4042_ = l_Lean_privateToUserName(v_declName_4023_);
                leanh::lean_inc_ref(v_env_4029_);
                v___x_4043_ = lean_is_reserved_name(v_env_4029_, v___x_4042_);
                if v___x_4043_ == 0 {
                    leanh::lean_inc(v_declName_4023_);
                    v___x_4044_ = l_Lean_mkPrivateName(v_____do__lift_4030_, v_declName_4023_);
                    v___x_4045_ = lean_is_reserved_name(v_env_4029_, v___x_4044_);
                    v___y_4032_ = v___x_4045_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_env_4029_);
                    v___y_4032_ = v___x_4043_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4032_ == 0 {
                    leanh::lean_dec(v___f_4028_);
                    leanh::lean_dec(v_toBind_4027_);
                    leanh::lean_dec_ref(v_inst_4026_);
                    leanh::lean_dec_ref(v_inst_4025_);
                    leanh::lean_dec(v_declName_4023_);
                    v___x_4033_ = leanh::lean_box(0);
                    v___x_4034_ = leanh::lean_apply_1(v___f_4022_, v___x_4033_);
                    return v___x_4034_;
                } else {
                    leanh::lean_dec(v___f_4022_);
                    v___x_4035_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once
                        ),
                        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1,
                    );
                    v___x_4036_ = l_Lean_MessageData_ofConstName(v_declName_4023_, v___x_4024_);
                    v___x_4037_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4037_, 0, v___x_4035_);
                    leanh::lean_ctor_set(v___x_4037_, 1, v___x_4036_);
                    v___x_4038_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once
                        ),
                        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3,
                    );
                    v___x_4039_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4039_, 0, v___x_4037_);
                    leanh::lean_ctor_set(v___x_4039_, 1, v___x_4038_);
                    v___x_4040_ =
                        l_Lean_throwError___redArg(v_inst_4025_, v_inst_4026_, v___x_4039_);
                    v___x_4041_ = leanh::lean_apply_4(
                        v_toBind_4027_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_4040_,
                        v___f_4028_,
                    );
                    return v___x_4041_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___boxed(
    mut v___f_4046_: *mut leanh::LeanObject,
    mut v_declName_4047_: *mut leanh::LeanObject,
    mut v___x_4048_: *mut leanh::LeanObject,
    mut v_inst_4049_: *mut leanh::LeanObject,
    mut v_inst_4050_: *mut leanh::LeanObject,
    mut v_toBind_4051_: *mut leanh::LeanObject,
    mut v___f_4052_: *mut leanh::LeanObject,
    mut v_env_4053_: *mut leanh::LeanObject,
    mut v_____do__lift_4054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1134__boxed_4055_: u8 = 0;
    let mut v_res_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1134__boxed_4055_ = (leanh::lean_unbox(v___x_4048_) as u8);
    v_res_4056_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9(
        v___f_4046_,
        v_declName_4047_,
        v___x_1134__boxed_4055_,
        v_inst_4049_,
        v_inst_4050_,
        v_toBind_4051_,
        v___f_4052_,
        v_env_4053_,
        v_____do__lift_4054_,
    );
    leanh::lean_dec_ref(v_____do__lift_4054_);
    return v_res_4056_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8(
    mut v_toBind_4057_: *mut leanh::LeanObject,
    mut v_getEnv_4058_: *mut leanh::LeanObject,
    mut v___f_4059_: *mut leanh::LeanObject,
    mut v_____r_4060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4061_ = leanh::lean_apply_4(
        v_toBind_4057_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_4058_,
        v___f_4059_,
    );
    return v___x_4061_;
}
pub unsafe fn _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4063_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__0;
    v___x_4064_ = l_Lean_stringToMessageData(v___x_4063_);
    return v___x_4064_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(
    mut v_declName_4065_: *mut leanh::LeanObject,
    mut v___x_4066_: u8,
    mut v_inst_4067_: *mut leanh::LeanObject,
    mut v_inst_4068_: *mut leanh::LeanObject,
    mut v_toBind_4069_: *mut leanh::LeanObject,
    mut v___f_4070_: *mut leanh::LeanObject,
    mut v___f_4071_: *mut leanh::LeanObject,
    mut v_____r_4072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_declName_4065_);
    v___x_4073_ = lean_private_to_user_name(v_declName_4065_);
    if leanh::lean_obj_tag(v___x_4073_) == 0 {
        let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_4071_);
        v___x_4074_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once
            ),
            _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1,
        );
        v___x_4075_ = l_Lean_MessageData_ofConstName(v_declName_4065_, v___x_4066_);
        v___x_4076_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4076_, 0, v___x_4074_);
        leanh::lean_ctor_set(v___x_4076_, 1, v___x_4075_);
        v___x_4077_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once
            ),
            _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3,
        );
        v___x_4078_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4078_, 0, v___x_4076_);
        leanh::lean_ctor_set(v___x_4078_, 1, v___x_4077_);
        v___x_4079_ = l_Lean_throwError___redArg(v_inst_4067_, v_inst_4068_, v___x_4078_);
        v___x_4080_ = leanh::lean_apply_4(
            v_toBind_4069_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4079_,
            v___f_4070_,
        );
        return v___x_4080_;
    } else {
        let mut v_val_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_4070_);
        leanh::lean_dec(v_declName_4065_);
        v_val_4081_ = leanh::lean_ctor_get(v___x_4073_, 0);
        leanh::lean_inc(v_val_4081_);
        leanh::lean_dec_ref_known(v___x_4073_, 1);
        v___x_4082_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once
            ),
            _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1,
        );
        v___x_4083_ = l_Lean_MessageData_ofConstName(v_val_4081_, v___x_4066_);
        v___x_4084_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4084_, 0, v___x_4082_);
        leanh::lean_ctor_set(v___x_4084_, 1, v___x_4083_);
        v___x_4085_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once
            ),
            _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3,
        );
        v___x_4086_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4086_, 0, v___x_4084_);
        leanh::lean_ctor_set(v___x_4086_, 1, v___x_4085_);
        v___x_4087_ = l_Lean_throwError___redArg(v_inst_4067_, v_inst_4068_, v___x_4086_);
        v___x_4088_ = leanh::lean_apply_4(
            v_toBind_4069_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4087_,
            v___f_4071_,
        );
        return v___x_4088_;
    }
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___boxed(
    mut v_declName_4089_: *mut leanh::LeanObject,
    mut v___x_4090_: *mut leanh::LeanObject,
    mut v_inst_4091_: *mut leanh::LeanObject,
    mut v_inst_4092_: *mut leanh::LeanObject,
    mut v_toBind_4093_: *mut leanh::LeanObject,
    mut v___f_4094_: *mut leanh::LeanObject,
    mut v___f_4095_: *mut leanh::LeanObject,
    mut v_____r_4096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1208__boxed_4097_: u8 = 0;
    let mut v_res_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1208__boxed_4097_ = (leanh::lean_unbox(v___x_4090_) as u8);
    v_res_4098_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11(
        v_declName_4089_,
        v___x_1208__boxed_4097_,
        v_inst_4091_,
        v_inst_4092_,
        v_toBind_4093_,
        v___f_4094_,
        v___f_4095_,
        v_____r_4096_,
    );
    return v_res_4098_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10(
    mut v_toMonadRef_4099_: *mut leanh::LeanObject,
    mut v_inst_4100_: *mut leanh::LeanObject,
    mut v_inst_4101_: *mut leanh::LeanObject,
    mut v_inst_4102_: *mut leanh::LeanObject,
    mut v_inst_4103_: *mut leanh::LeanObject,
    mut v_toBind_4104_: *mut leanh::LeanObject,
    mut v_declName_4105_: *mut leanh::LeanObject,
    mut v_toPure_4106_: *mut leanh::LeanObject,
    mut v_getEnv_4107_: *mut leanh::LeanObject,
    mut v_inst_4108_: *mut leanh::LeanObject,
    mut v_env_4109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addInfo_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: u8 = 0;
    let mut v___x_4121_: u8 = 0;
    v___x_4110_ = 0;
    v___x_4111_ = leanh::lean_box((v___x_4110_) as usize);
    leanh::lean_inc_n(v_toBind_4104_, 4);
    leanh::lean_inc_ref_n(v_inst_4103_, 4);
    leanh::lean_inc_ref(v_inst_4102_);
    leanh::lean_inc_ref(v_inst_4101_);
    leanh::lean_inc_ref_n(v_inst_4100_, 4);
    leanh::lean_inc_ref(v_toMonadRef_4099_);
    v_addInfo_4112_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v_addInfo_4112_, 0, v_toMonadRef_4099_);
    leanh::lean_closure_set(v_addInfo_4112_, 1, v___x_4111_);
    leanh::lean_closure_set(v_addInfo_4112_, 2, v_inst_4100_);
    leanh::lean_closure_set(v_addInfo_4112_, 3, v_inst_4101_);
    leanh::lean_closure_set(v_addInfo_4112_, 4, v_inst_4102_);
    leanh::lean_closure_set(v_addInfo_4112_, 5, v_inst_4103_);
    leanh::lean_closure_set(v_addInfo_4112_, 6, v_toBind_4104_);
    v_env_4113_ = l_Lean_Environment_setExporting(v_env_4109_, v___x_4110_);
    leanh::lean_inc_ref(v_addInfo_4112_);
    leanh::lean_inc_ref_n(v_env_4113_, 4);
    leanh::lean_inc_n(v_declName_4105_, 4);
    v___f_4114_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__4 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_4114_, 0, v_declName_4105_);
    leanh::lean_closure_set(v___f_4114_, 1, v_toPure_4106_);
    leanh::lean_closure_set(v___f_4114_, 2, v_env_4113_);
    leanh::lean_closure_set(v___f_4114_, 3, v_inst_4100_);
    leanh::lean_closure_set(v___f_4114_, 4, v_inst_4103_);
    leanh::lean_closure_set(v___f_4114_, 5, v_addInfo_4112_);
    leanh::lean_closure_set(v___f_4114_, 6, v_toBind_4104_);
    leanh::lean_inc_ref(v___f_4114_);
    v___f_4115_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4115_, 0, v___f_4114_);
    v___f_4116_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__7 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_4116_, 0, v_env_4113_);
    leanh::lean_closure_set(v___f_4116_, 1, v_declName_4105_);
    leanh::lean_closure_set(v___f_4116_, 2, v___f_4114_);
    leanh::lean_closure_set(v___f_4116_, 3, v_inst_4100_);
    leanh::lean_closure_set(v___f_4116_, 4, v_inst_4103_);
    leanh::lean_closure_set(v___f_4116_, 5, v_toBind_4104_);
    leanh::lean_closure_set(v___f_4116_, 6, v___f_4115_);
    leanh::lean_closure_set(v___f_4116_, 7, v_addInfo_4112_);
    leanh::lean_inc_ref(v___f_4116_);
    v___f_4117_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4117_, 0, v___f_4116_);
    v___x_4118_ = leanh::lean_box((v___x_4110_) as usize);
    v___f_4119_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_4119_, 0, v___f_4116_);
    leanh::lean_closure_set(v___f_4119_, 1, v_declName_4105_);
    leanh::lean_closure_set(v___f_4119_, 2, v___x_4118_);
    leanh::lean_closure_set(v___f_4119_, 3, v_inst_4100_);
    leanh::lean_closure_set(v___f_4119_, 4, v_inst_4103_);
    leanh::lean_closure_set(v___f_4119_, 5, v_toBind_4104_);
    leanh::lean_closure_set(v___f_4119_, 6, v___f_4117_);
    leanh::lean_closure_set(v___f_4119_, 7, v_env_4113_);
    v___x_4120_ = 1;
    v___x_4121_ = l_Lean_Environment_contains(v_env_4113_, v_declName_4105_, v___x_4120_);
    if v___x_4121_ == 0 {
        let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_declName_4105_);
        leanh::lean_dec_ref(v_inst_4103_);
        leanh::lean_dec_ref(v_inst_4101_);
        leanh::lean_dec_ref(v_toMonadRef_4099_);
        v___x_4122_ = leanh::lean_apply_4(
            v_toBind_4104_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_4107_,
            v___f_4119_,
        );
        v___x_4123_ = l_Lean_withEnv___redArg(
            v_inst_4100_,
            v_inst_4108_,
            v_inst_4102_,
            v_env_4113_,
            v___x_4122_,
        );
        return v___x_4123_;
    } else {
        let mut v___f_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_n(v_toBind_4104_, 3);
        v___f_4124_ = leanh::lean_alloc_closure(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__8 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_4124_, 0, v_toBind_4104_);
        leanh::lean_closure_set(v___f_4124_, 1, v_getEnv_4107_);
        leanh::lean_closure_set(v___f_4124_, 2, v___f_4119_);
        v___x_4125_ = leanh::lean_box((v___x_4120_) as usize);
        leanh::lean_inc_ref(v___f_4124_);
        leanh::lean_inc_ref(v_inst_4103_);
        leanh::lean_inc_ref_n(v_inst_4100_, 2);
        leanh::lean_inc(v_declName_4105_);
        v___f_4126_ = leanh::lean_alloc_closure(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___boxed
                as *mut core::ffi::c_void,
            8,
            7,
        );
        leanh::lean_closure_set(v___f_4126_, 0, v_declName_4105_);
        leanh::lean_closure_set(v___f_4126_, 1, v___x_4125_);
        leanh::lean_closure_set(v___f_4126_, 2, v_inst_4100_);
        leanh::lean_closure_set(v___f_4126_, 3, v_inst_4103_);
        leanh::lean_closure_set(v___f_4126_, 4, v_toBind_4104_);
        leanh::lean_closure_set(v___f_4126_, 5, v___f_4124_);
        leanh::lean_closure_set(v___f_4126_, 6, v___f_4124_);
        leanh::lean_inc_ref(v_inst_4102_);
        v___x_4127_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__2(
            v_toMonadRef_4099_,
            v___x_4110_,
            v_inst_4100_,
            v_inst_4101_,
            v_inst_4102_,
            v_inst_4103_,
            v_toBind_4104_,
            v_declName_4105_,
        );
        v___x_4128_ = leanh::lean_apply_4(
            v_toBind_4104_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4127_,
            v___f_4126_,
        );
        v___x_4129_ = l_Lean_withEnv___redArg(
            v_inst_4100_,
            v_inst_4108_,
            v_inst_4102_,
            v_env_4113_,
            v___x_4128_,
        );
        return v___x_4129_;
    }
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___redArg(
    mut v_inst_4130_: *mut leanh::LeanObject,
    mut v_inst_4131_: *mut leanh::LeanObject,
    mut v_inst_4132_: *mut leanh::LeanObject,
    mut v_inst_4133_: *mut leanh::LeanObject,
    mut v_inst_4134_: *mut leanh::LeanObject,
    mut v_declName_4135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4136_ = leanh::lean_ctor_get(v_inst_4130_, 0);
    v_toBind_4137_ = leanh::lean_ctor_get(v_inst_4130_, 1);
    leanh::lean_inc_n(v_toBind_4137_, 2);
    v_getEnv_4138_ = leanh::lean_ctor_get(v_inst_4131_, 0);
    leanh::lean_inc_n(v_getEnv_4138_, 2);
    v_toMonadRef_4139_ = leanh::lean_ctor_get(v_inst_4132_, 1);
    leanh::lean_inc_ref(v_toMonadRef_4139_);
    v_toPure_4140_ = leanh::lean_ctor_get(v_toApplicative_4136_, 1);
    leanh::lean_inc(v_toPure_4140_);
    v___f_4141_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__10 as *mut core::ffi::c_void,
        11,
        10,
    );
    leanh::lean_closure_set(v___f_4141_, 0, v_toMonadRef_4139_);
    leanh::lean_closure_set(v___f_4141_, 1, v_inst_4130_);
    leanh::lean_closure_set(v___f_4141_, 2, v_inst_4134_);
    leanh::lean_closure_set(v___f_4141_, 3, v_inst_4131_);
    leanh::lean_closure_set(v___f_4141_, 4, v_inst_4132_);
    leanh::lean_closure_set(v___f_4141_, 5, v_toBind_4137_);
    leanh::lean_closure_set(v___f_4141_, 6, v_declName_4135_);
    leanh::lean_closure_set(v___f_4141_, 7, v_toPure_4140_);
    leanh::lean_closure_set(v___f_4141_, 8, v_getEnv_4138_);
    leanh::lean_closure_set(v___f_4141_, 9, v_inst_4133_);
    v___x_4142_ = leanh::lean_apply_4(
        v_toBind_4137_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_4138_,
        v___f_4141_,
    );
    return v___x_4142_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared(
    mut v_m_4143_: *mut leanh::LeanObject,
    mut v_inst_4144_: *mut leanh::LeanObject,
    mut v_inst_4145_: *mut leanh::LeanObject,
    mut v_inst_4146_: *mut leanh::LeanObject,
    mut v_inst_4147_: *mut leanh::LeanObject,
    mut v_inst_4148_: *mut leanh::LeanObject,
    mut v_declName_4149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4150_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(
        v_inst_4144_,
        v_inst_4145_,
        v_inst_4146_,
        v_inst_4147_,
        v_inst_4148_,
        v_declName_4149_,
    );
    return v___x_4150_;
}
pub unsafe fn l_Lean_Elab_Visibility_ctorIdx(mut v_x_4151_: u8) -> *mut leanh::LeanObject {
    match v_x_4151_ {
        0 => {
            let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4152_ = leanh::lean_unsigned_to_nat(0);
            return v___x_4152_;
        }
        1 => {
            let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4153_ = leanh::lean_unsigned_to_nat(1);
            return v___x_4153_;
        }
        _ => {
            let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4154_ = leanh::lean_unsigned_to_nat(2);
            return v___x_4154_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Visibility_ctorIdx___boxed(
    mut v_x_4155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_4156_: u8 = 0;
    let mut v_res_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4156_ = (leanh::lean_unbox(v_x_4155_) as u8);
    v_res_4157_ = l_Lean_Elab_Visibility_ctorIdx(v_x_boxed_4156_);
    return v_res_4157_;
}
pub unsafe fn l_Lean_Elab_Visibility_toCtorIdx(mut v_x_4158_: u8) -> *mut leanh::LeanObject {
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = l_Lean_Elab_Visibility_ctorIdx(v_x_4158_);
    return v___x_4159_;
}
pub unsafe fn l_Lean_Elab_Visibility_toCtorIdx___boxed(
    mut v_x_4160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_4161_: u8 = 0;
    let mut v_res_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4161_ = (leanh::lean_unbox(v_x_4160_) as u8);
    v_res_4162_ = l_Lean_Elab_Visibility_toCtorIdx(v_x_4__boxed_4161_);
    return v_res_4162_;
}
pub unsafe fn l_Lean_Elab_Visibility_ctorElim___redArg(
    mut v_k_4163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_4163_);
    return v_k_4163_;
}
pub unsafe fn l_Lean_Elab_Visibility_ctorElim___redArg___boxed(
    mut v_k_4164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4165_ = l_Lean_Elab_Visibility_ctorElim___redArg(v_k_4164_);
    leanh::lean_dec(v_k_4164_);
    return v_res_4165_;
}
pub unsafe fn l_Lean_Elab_Visibility_ctorElim(
    mut v_motive_4166_: *mut leanh::LeanObject,
    mut v_ctorIdx_4167_: *mut leanh::LeanObject,
    mut v_t_4168_: u8,
    mut v_h_4169_: *mut leanh::LeanObject,
    mut v_k_4170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_4170_);
    return v_k_4170_;
}
pub unsafe fn l_Lean_Elab_Visibility_ctorElim___boxed(
    mut v_motive_4171_: *mut leanh::LeanObject,
    mut v_ctorIdx_4172_: *mut leanh::LeanObject,
    mut v_t_4173_: *mut leanh::LeanObject,
    mut v_h_4174_: *mut leanh::LeanObject,
    mut v_k_4175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4176_: u8 = 0;
    let mut v_res_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4176_ = (leanh::lean_unbox(v_t_4173_) as u8);
    v_res_4177_ = l_Lean_Elab_Visibility_ctorElim(
        v_motive_4171_,
        v_ctorIdx_4172_,
        v_t_boxed_4176_,
        v_h_4174_,
        v_k_4175_,
    );
    leanh::lean_dec(v_k_4175_);
    leanh::lean_dec(v_ctorIdx_4172_);
    return v_res_4177_;
}
pub unsafe fn l_Lean_Elab_Visibility_regular_elim___redArg(
    mut v_regular_4178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_regular_4178_);
    return v_regular_4178_;
}
pub unsafe fn l_Lean_Elab_Visibility_regular_elim___redArg___boxed(
    mut v_regular_4179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4180_ = l_Lean_Elab_Visibility_regular_elim___redArg(v_regular_4179_);
    leanh::lean_dec(v_regular_4179_);
    return v_res_4180_;
}
pub unsafe fn l_Lean_Elab_Visibility_regular_elim(
    mut v_motive_4181_: *mut leanh::LeanObject,
    mut v_t_4182_: u8,
    mut v_h_4183_: *mut leanh::LeanObject,
    mut v_regular_4184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_regular_4184_);
    return v_regular_4184_;
}
pub unsafe fn l_Lean_Elab_Visibility_regular_elim___boxed(
    mut v_motive_4185_: *mut leanh::LeanObject,
    mut v_t_4186_: *mut leanh::LeanObject,
    mut v_h_4187_: *mut leanh::LeanObject,
    mut v_regular_4188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4189_: u8 = 0;
    let mut v_res_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4189_ = (leanh::lean_unbox(v_t_4186_) as u8);
    v_res_4190_ = l_Lean_Elab_Visibility_regular_elim(
        v_motive_4185_,
        v_t_boxed_4189_,
        v_h_4187_,
        v_regular_4188_,
    );
    leanh::lean_dec(v_regular_4188_);
    return v_res_4190_;
}
pub unsafe fn l_Lean_Elab_Visibility_private_elim___redArg(
    mut v_private_4191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_private_4191_);
    return v_private_4191_;
}
pub unsafe fn l_Lean_Elab_Visibility_private_elim___redArg___boxed(
    mut v_private_4192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4193_ = l_Lean_Elab_Visibility_private_elim___redArg(v_private_4192_);
    leanh::lean_dec(v_private_4192_);
    return v_res_4193_;
}
pub unsafe fn l_Lean_Elab_Visibility_private_elim(
    mut v_motive_4194_: *mut leanh::LeanObject,
    mut v_t_4195_: u8,
    mut v_h_4196_: *mut leanh::LeanObject,
    mut v_private_4197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_private_4197_);
    return v_private_4197_;
}
pub unsafe fn l_Lean_Elab_Visibility_private_elim___boxed(
    mut v_motive_4198_: *mut leanh::LeanObject,
    mut v_t_4199_: *mut leanh::LeanObject,
    mut v_h_4200_: *mut leanh::LeanObject,
    mut v_private_4201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4202_: u8 = 0;
    let mut v_res_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4202_ = (leanh::lean_unbox(v_t_4199_) as u8);
    v_res_4203_ = l_Lean_Elab_Visibility_private_elim(
        v_motive_4198_,
        v_t_boxed_4202_,
        v_h_4200_,
        v_private_4201_,
    );
    leanh::lean_dec(v_private_4201_);
    return v_res_4203_;
}
pub unsafe fn l_Lean_Elab_Visibility_public_elim___redArg(
    mut v_public_4204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_public_4204_);
    return v_public_4204_;
}
pub unsafe fn l_Lean_Elab_Visibility_public_elim___redArg___boxed(
    mut v_public_4205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4206_ = l_Lean_Elab_Visibility_public_elim___redArg(v_public_4205_);
    leanh::lean_dec(v_public_4205_);
    return v_res_4206_;
}
pub unsafe fn l_Lean_Elab_Visibility_public_elim(
    mut v_motive_4207_: *mut leanh::LeanObject,
    mut v_t_4208_: u8,
    mut v_h_4209_: *mut leanh::LeanObject,
    mut v_public_4210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_public_4210_);
    return v_public_4210_;
}
pub unsafe fn l_Lean_Elab_Visibility_public_elim___boxed(
    mut v_motive_4211_: *mut leanh::LeanObject,
    mut v_t_4212_: *mut leanh::LeanObject,
    mut v_h_4213_: *mut leanh::LeanObject,
    mut v_public_4214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4215_: u8 = 0;
    let mut v_res_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4215_ = (leanh::lean_unbox(v_t_4212_) as u8);
    v_res_4216_ = l_Lean_Elab_Visibility_public_elim(
        v_motive_4211_,
        v_t_boxed_4215_,
        v_h_4213_,
        v_public_4214_,
    );
    leanh::lean_dec(v_public_4214_);
    return v_res_4216_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedVisibility_default() -> u8 {
    let mut v___x_4217_: u8 = 0;
    v___x_4217_ = 0;
    return v___x_4217_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedVisibility() -> u8 {
    let mut v___x_4218_: u8 = 0;
    v___x_4218_ = 0;
    return v___x_4218_;
}
pub unsafe fn l_Lean_Elab_instToStringVisibility___lam__0(
    mut v_x_4222_: u8,
) -> *mut leanh::LeanObject {
    match v_x_4222_ {
        0 => {
            let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4223_ = l_Lean_Elab_instToStringVisibility___lam__0___closed__0;
            return v___x_4223_;
        }
        1 => {
            let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4224_ = l_Lean_Elab_instToStringVisibility___lam__0___closed__1;
            return v___x_4224_;
        }
        _ => {
            let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4225_ = l_Lean_Elab_instToStringVisibility___lam__0___closed__2;
            return v___x_4225_;
        }
    }
}
pub unsafe fn l_Lean_Elab_instToStringVisibility___lam__0___boxed(
    mut v_x_4226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_36__boxed_4227_: u8 = 0;
    let mut v_res_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_4227_ = (leanh::lean_unbox(v_x_4226_) as u8);
    v_res_4228_ = l_Lean_Elab_instToStringVisibility___lam__0(v_x_36__boxed_4227_);
    return v_res_4228_;
}
pub unsafe fn l_Lean_Elab_Visibility_isPrivate(mut v_x_4231_: u8) -> u8 {
    if v_x_4231_ == 1 {
        let mut v___x_4232_: u8 = 0;
        v___x_4232_ = 1;
        return v___x_4232_;
    } else {
        let mut v___x_4233_: u8 = 0;
        v___x_4233_ = 0;
        return v___x_4233_;
    }
}
pub unsafe fn l_Lean_Elab_Visibility_isPrivate___boxed(
    mut v_x_4234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_21__boxed_4235_: u8 = 0;
    let mut v_res_4236_: u8 = 0;
    let mut v_r_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_4235_ = (leanh::lean_unbox(v_x_4234_) as u8);
    v_res_4236_ = l_Lean_Elab_Visibility_isPrivate(v_x_21__boxed_4235_);
    v_r_4237_ = leanh::lean_box((v_res_4236_) as usize);
    return v_r_4237_;
}
pub unsafe fn l_Lean_Elab_Visibility_isPublic(mut v_x_4238_: u8) -> u8 {
    if v_x_4238_ == 2 {
        let mut v___x_4239_: u8 = 0;
        v___x_4239_ = 1;
        return v___x_4239_;
    } else {
        let mut v___x_4240_: u8 = 0;
        v___x_4240_ = 0;
        return v___x_4240_;
    }
}
pub unsafe fn l_Lean_Elab_Visibility_isPublic___boxed(
    mut v_x_4241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_21__boxed_4242_: u8 = 0;
    let mut v_res_4243_: u8 = 0;
    let mut v_r_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_4242_ = (leanh::lean_unbox(v_x_4241_) as u8);
    v_res_4243_ = l_Lean_Elab_Visibility_isPublic(v_x_21__boxed_4242_);
    v_r_4244_ = leanh::lean_box((v_res_4243_) as usize);
    return v_r_4244_;
}
pub unsafe fn l_Lean_Elab_Visibility_isInferredPublic(
    mut v_env_4245_: *mut leanh::LeanObject,
    mut v_v_4246_: u8,
) -> u8 {
    let mut v___y_4248_: u8 = 0;
    let mut v___x_4249_: u8 = 0;
    let mut v___x_4250_: u8 = 0;
    let mut v_isExporting_4251_: u8 = 0;
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_4253_: u8 = 0;
    let mut v___x_4254_: u8 = 0;
    let mut v___x_4255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isExporting_4251_ = leanh::lean_ctor_get_uint8(
                    v_env_4245_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                if v_isExporting_4251_ == 0 {
                    v___x_4252_ = l_Lean_Environment_header(v_env_4245_);
                    v_isModule_4253_ = leanh::lean_ctor_get_uint8(
                        v___x_4252_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                    );
                    leanh::lean_dec_ref(v___x_4252_);
                    if v_isModule_4253_ == 0 {
                        v___x_4254_ = 1;
                        v___y_4248_ = v___x_4254_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4255_ = l_Lean_Elab_Visibility_isPublic(v_v_4246_);
                        return v___x_4255_;
                    }
                } else {
                    v___y_4248_ = v_isExporting_4251_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4249_ = l_Lean_Elab_Visibility_isPrivate(v_v_4246_);
                if v___x_4249_ == 0 {
                    return v___y_4248_;
                } else {
                    v___x_4250_ = 0;
                    return v___x_4250_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Visibility_isInferredPublic___boxed(
    mut v_env_4256_: *mut leanh::LeanObject,
    mut v_v_4257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_4258_: u8 = 0;
    let mut v_res_4259_: u8 = 0;
    let mut v_r_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_4258_ = (leanh::lean_unbox(v_v_4257_) as u8);
    v_res_4259_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_4256_, v_v_boxed_4258_);
    leanh::lean_dec_ref(v_env_4256_);
    v_r_4260_ = leanh::lean_box((v_res_4259_) as usize);
    return v_r_4260_;
}
pub unsafe fn l_Lean_Elab_elabVisibility___redArg___lam__0(
    mut v_toPure_4261_: *mut leanh::LeanObject,
    mut v_____r_4262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4263_: u8 = 0;
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4263_ = 2;
    v___x_4264_ = leanh::lean_box((v___x_4263_) as usize);
    v___x_4265_ =
        leanh::lean_apply_2(v_toPure_4261_, leanh::lean_box(0), v___x_4264_);
    return v___x_4265_;
}
pub unsafe fn l_Lean_Elab_elabVisibility___redArg___lam__2(
    mut v_toPure_4266_: *mut leanh::LeanObject,
    mut v_____r_4267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4268_: u8 = 0;
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4268_ = 1;
    v___x_4269_ = leanh::lean_box((v___x_4268_) as usize);
    v___x_4270_ =
        leanh::lean_apply_2(v_toPure_4266_, leanh::lean_box(0), v___x_4269_);
    return v___x_4270_;
}
pub unsafe fn _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4272_ = l_Lean_Elab_elabVisibility___redArg___lam__3___closed__0;
    v___x_4273_ = l_Lean_stringToMessageData(v___x_4272_);
    return v___x_4273_;
}
pub unsafe fn _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4275_ = l_Lean_Elab_elabVisibility___redArg___lam__3___closed__2;
    v___x_4276_ = l_Lean_stringToMessageData(v___x_4275_);
    return v___x_4276_;
}
pub unsafe fn _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4292_ = l_Lean_Elab_elabVisibility___redArg___lam__3___closed__10;
    v___x_4293_ = l_Lean_stringToMessageData(v___x_4292_);
    return v___x_4293_;
}
pub unsafe fn _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4295_ = l_Lean_Elab_elabVisibility___redArg___lam__3___closed__12;
    v___x_4296_ = l_Lean_stringToMessageData(v___x_4295_);
    return v___x_4296_;
}
pub unsafe fn l_Lean_Elab_elabVisibility___redArg___lam__3(
    mut v_vis_x3f_4297_: *mut leanh::LeanObject,
    mut v_toPure_4298_: *mut leanh::LeanObject,
    mut v_inst_4299_: *mut leanh::LeanObject,
    mut v_inst_4300_: *mut leanh::LeanObject,
    mut v_inst_4301_: *mut leanh::LeanObject,
    mut v_inst_4302_: *mut leanh::LeanObject,
    mut v_inst_4303_: *mut leanh::LeanObject,
    mut v_inst_4304_: *mut leanh::LeanObject,
    mut v_toBind_4305_: *mut leanh::LeanObject,
    mut v___f_4306_: *mut leanh::LeanObject,
    mut v___f_4307_: *mut leanh::LeanObject,
    mut v___f_4308_: *mut leanh::LeanObject,
    mut v___f_4309_: *mut leanh::LeanObject,
    mut v_env_4310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: u8 = 0;
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_4330_: u8 = 0;
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4336_: u8 = 0;
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_4338_: u8 = 0;
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: u8 = 0;
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: u8 = 0;
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_4352_: u8 = 0;
    let mut v_isExporting_4353_: u8 = 0;
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_vis_x3f_4297_) == 0 {
                    leanh::lean_dec(v___f_4309_);
                    leanh::lean_dec(v___f_4308_);
                    leanh::lean_dec(v___f_4307_);
                    leanh::lean_dec(v___f_4306_);
                    leanh::lean_dec(v_toBind_4305_);
                    leanh::lean_dec_ref(v_inst_4304_);
                    leanh::lean_dec(v_inst_4303_);
                    leanh::lean_dec(v_inst_4302_);
                    leanh::lean_dec_ref(v_inst_4301_);
                    leanh::lean_dec_ref(v_inst_4300_);
                    leanh::lean_dec_ref(v_inst_4299_);
                    v___x_4314_ = 0;
                    v___x_4315_ = leanh::lean_box((v___x_4314_) as usize);
                    v___x_4316_ = leanh::lean_apply_2(
                        v_toPure_4298_,
                        leanh::lean_box(0),
                        v___x_4315_,
                    );
                    return v___x_4316_;
                } else {
                    leanh::lean_dec(v_toPure_4298_);
                    v_val_4317_ = leanh::lean_ctor_get(v_vis_x3f_4297_, 0);
                    leanh::lean_inc_n(v_val_4317_, 2);
                    leanh::lean_dec_ref_known(v_vis_x3f_4297_, 1);
                    v___x_4341_ = l_Lean_Elab_elabVisibility___redArg___lam__3___closed__8;
                    v___x_4342_ = l_Lean_Syntax_isOfKind(v_val_4317_, v___x_4341_);
                    if v___x_4342_ == 0 {
                        leanh::lean_dec(v___f_4309_);
                        leanh::lean_dec(v___f_4308_);
                        v___x_4343_ = l_Lean_Elab_elabVisibility___redArg___lam__3___closed__9;
                        leanh::lean_inc(v_val_4317_);
                        v___x_4344_ = l_Lean_Syntax_isOfKind(v_val_4317_, v___x_4343_);
                        if v___x_4344_ == 0 {
                            leanh::lean_dec(v___f_4307_);
                            leanh::lean_dec(v___f_4306_);
                            leanh::lean_dec(v_toBind_4305_);
                            leanh::lean_dec_ref(v_inst_4304_);
                            leanh::lean_dec(v_inst_4303_);
                            leanh::lean_dec(v_inst_4302_);
                            leanh::lean_dec_ref(v_inst_4301_);
                            v___x_4345_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11_once
                                ),
                                _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__11,
                            );
                            v___x_4346_ = l_Lean_throwErrorAt___redArg(
                                v_inst_4299_,
                                v_inst_4300_,
                                v_val_4317_,
                                v___x_4345_,
                            );
                            return v___x_4346_;
                        } else {
                            leanh::lean_dec_ref(v_inst_4300_);
                            v___x_4347_ = l_Lean_Syntax_getHeadInfo(v_val_4317_);
                            if leanh::lean_obj_tag(v___x_4347_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4347_, 4);
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_4347_);
                                if v___x_4342_ == 0 {
                                    leanh::lean_dec(v_val_4317_);
                                    leanh::lean_dec(v___f_4306_);
                                    leanh::lean_dec(v_toBind_4305_);
                                    leanh::lean_dec_ref(v_inst_4304_);
                                    leanh::lean_dec(v_inst_4303_);
                                    leanh::lean_dec(v_inst_4302_);
                                    leanh::lean_dec_ref(v_inst_4301_);
                                    leanh::lean_dec_ref(v_inst_4299_);
                                    v___x_4348_ = leanh::lean_box(0);
                                    v___x_4349_ =
                                        leanh::lean_apply_1(v___f_4307_, v___x_4348_);
                                    return v___x_4349_;
                                } else {
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___f_4307_);
                        leanh::lean_dec(v___f_4306_);
                        leanh::lean_dec_ref(v_inst_4300_);
                        v___x_4350_ = l_Lean_Syntax_getHeadInfo(v_val_4317_);
                        if leanh::lean_obj_tag(v___x_4350_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4350_, 4);
                            v___x_4351_ = l_Lean_Environment_header(v_env_4310_);
                            v_isModule_4352_ = leanh::lean_ctor_get_uint8(
                                v___x_4351_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4)
                                    as u32,
                            );
                            leanh::lean_dec_ref(v___x_4351_);
                            if v_isModule_4352_ == 0 {
                                leanh::lean_dec(v_val_4317_);
                                leanh::lean_dec(v___f_4309_);
                                leanh::lean_dec(v_toBind_4305_);
                                leanh::lean_dec_ref(v_inst_4304_);
                                leanh::lean_dec(v_inst_4303_);
                                leanh::lean_dec(v_inst_4302_);
                                leanh::lean_dec_ref(v_inst_4301_);
                                leanh::lean_dec_ref(v_inst_4299_);
                                state = 1;
                                continue;
                            } else {
                                v_isExporting_4353_ = leanh::lean_ctor_get_uint8(
                                    v_env_4310_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8)
                                        as u32,
                                );
                                if v_isExporting_4353_ == 0 {
                                    leanh::lean_dec(v___f_4308_);
                                    v___x_4354_ = l_Lean_linter_redundantVisibility;
                                    v___x_4355_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13_once), _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__13);
                                    v___x_4356_ = l_Lean_Linter_logLintIf___redArg(
                                        v_inst_4299_,
                                        v_inst_4301_,
                                        v_inst_4302_,
                                        v_inst_4303_,
                                        v_inst_4304_,
                                        v___x_4354_,
                                        v_val_4317_,
                                        v___x_4355_,
                                    );
                                    v___x_4357_ = leanh::lean_apply_4(
                                        v_toBind_4305_,
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_4356_,
                                        v___f_4309_,
                                    );
                                    return v___x_4357_;
                                } else {
                                    leanh::lean_dec(v_val_4317_);
                                    leanh::lean_dec(v___f_4309_);
                                    leanh::lean_dec(v_toBind_4305_);
                                    leanh::lean_dec_ref(v_inst_4304_);
                                    leanh::lean_dec(v_inst_4303_);
                                    leanh::lean_dec(v_inst_4302_);
                                    leanh::lean_dec_ref(v_inst_4301_);
                                    leanh::lean_dec_ref(v_inst_4299_);
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_4350_);
                            leanh::lean_dec(v_val_4317_);
                            leanh::lean_dec(v___f_4309_);
                            leanh::lean_dec(v_toBind_4305_);
                            leanh::lean_dec_ref(v_inst_4304_);
                            leanh::lean_dec(v_inst_4303_);
                            leanh::lean_dec(v_inst_4302_);
                            leanh::lean_dec_ref(v_inst_4301_);
                            leanh::lean_dec_ref(v_inst_4299_);
                            v___x_4358_ = leanh::lean_box(0);
                            v___x_4359_ = leanh::lean_apply_1(v___f_4308_, v___x_4358_);
                            return v___x_4359_;
                        }
                    }
                }
            }
            1 => {
                v___x_4312_ = leanh::lean_box(0);
                v___x_4313_ = leanh::lean_apply_1(v___f_4308_, v___x_4312_);
                return v___x_4313_;
            }
            2 => {
                leanh::lean_inc_ref(v___y_4321_);
                v___x_4322_ = l_Lean_stringToMessageData(v___y_4321_);
                leanh::lean_inc_ref(v___y_4319_);
                v___x_4323_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4323_, 0, v___y_4319_);
                leanh::lean_ctor_set(v___x_4323_, 1, v___x_4322_);
                v___x_4324_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1_once
                    ),
                    _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__1,
                );
                v___x_4325_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4325_, 0, v___x_4323_);
                leanh::lean_ctor_set(v___x_4325_, 1, v___x_4324_);
                leanh::lean_inc_ref(v___y_4320_);
                v___x_4326_ = l_Lean_Linter_logLintIf___redArg(
                    v_inst_4299_,
                    v_inst_4301_,
                    v_inst_4302_,
                    v_inst_4303_,
                    v_inst_4304_,
                    v___y_4320_,
                    v_val_4317_,
                    v___x_4325_,
                );
                v___x_4327_ = leanh::lean_apply_4(
                    v_toBind_4305_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4326_,
                    v___f_4306_,
                );
                return v___x_4327_;
            }
            3 => {
                v___x_4329_ = l_Lean_Environment_header(v_env_4310_);
                v_isModule_4330_ = leanh::lean_ctor_get_uint8(
                    v___x_4329_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                );
                leanh::lean_dec_ref(v___x_4329_);
                v___x_4331_ = l_Lean_linter_redundantVisibility;
                v___x_4332_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3_once
                    ),
                    _init_l_Lean_Elab_elabVisibility___redArg___lam__3___closed__3,
                );
                if v_isModule_4330_ == 0 {
                    v___x_4333_ = l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4;
                    v___y_4319_ = v___x_4332_;
                    v___y_4320_ = v___x_4331_;
                    v___y_4321_ = v___x_4333_;
                    state = 2;
                    continue;
                } else {
                    v___x_4334_ = l_Lean_Elab_elabVisibility___redArg___lam__3___closed__5;
                    v___y_4319_ = v___x_4332_;
                    v___y_4320_ = v___x_4331_;
                    v___y_4321_ = v___x_4334_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_isExporting_4336_ = leanh::lean_ctor_get_uint8(
                    v_env_4310_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                if v_isExporting_4336_ == 0 {
                    v___x_4337_ = l_Lean_Environment_header(v_env_4310_);
                    v_isModule_4338_ = leanh::lean_ctor_get_uint8(
                        v___x_4337_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                    );
                    leanh::lean_dec_ref(v___x_4337_);
                    if v_isModule_4338_ == 0 {
                        leanh::lean_dec(v___f_4307_);
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_4317_);
                        leanh::lean_dec(v___f_4306_);
                        leanh::lean_dec(v_toBind_4305_);
                        leanh::lean_dec_ref(v_inst_4304_);
                        leanh::lean_dec(v_inst_4303_);
                        leanh::lean_dec(v_inst_4302_);
                        leanh::lean_dec_ref(v_inst_4301_);
                        leanh::lean_dec_ref(v_inst_4299_);
                        v___x_4339_ = leanh::lean_box(0);
                        v___x_4340_ = leanh::lean_apply_1(v___f_4307_, v___x_4339_);
                        return v___x_4340_;
                    }
                } else {
                    leanh::lean_dec(v___f_4307_);
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabVisibility___redArg___lam__3___boxed(
    mut v_vis_x3f_4360_: *mut leanh::LeanObject,
    mut v_toPure_4361_: *mut leanh::LeanObject,
    mut v_inst_4362_: *mut leanh::LeanObject,
    mut v_inst_4363_: *mut leanh::LeanObject,
    mut v_inst_4364_: *mut leanh::LeanObject,
    mut v_inst_4365_: *mut leanh::LeanObject,
    mut v_inst_4366_: *mut leanh::LeanObject,
    mut v_inst_4367_: *mut leanh::LeanObject,
    mut v_toBind_4368_: *mut leanh::LeanObject,
    mut v___f_4369_: *mut leanh::LeanObject,
    mut v___f_4370_: *mut leanh::LeanObject,
    mut v___f_4371_: *mut leanh::LeanObject,
    mut v___f_4372_: *mut leanh::LeanObject,
    mut v_env_4373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4374_ = l_Lean_Elab_elabVisibility___redArg___lam__3(
        v_vis_x3f_4360_,
        v_toPure_4361_,
        v_inst_4362_,
        v_inst_4363_,
        v_inst_4364_,
        v_inst_4365_,
        v_inst_4366_,
        v_inst_4367_,
        v_toBind_4368_,
        v___f_4369_,
        v___f_4370_,
        v___f_4371_,
        v___f_4372_,
        v_env_4373_,
    );
    leanh::lean_dec_ref(v_env_4373_);
    return v_res_4374_;
}
pub unsafe fn l_Lean_Elab_elabVisibility___redArg(
    mut v_inst_4375_: *mut leanh::LeanObject,
    mut v_inst_4376_: *mut leanh::LeanObject,
    mut v_inst_4377_: *mut leanh::LeanObject,
    mut v_inst_4378_: *mut leanh::LeanObject,
    mut v_inst_4379_: *mut leanh::LeanObject,
    mut v_inst_4380_: *mut leanh::LeanObject,
    mut v_vis_x3f_4381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4382_ = leanh::lean_ctor_get(v_inst_4375_, 0);
    v_toBind_4383_ = leanh::lean_ctor_get(v_inst_4375_, 1);
    leanh::lean_inc_n(v_toBind_4383_, 2);
    v_getEnv_4384_ = leanh::lean_ctor_get(v_inst_4377_, 0);
    leanh::lean_inc(v_getEnv_4384_);
    v_toPure_4385_ = leanh::lean_ctor_get(v_toApplicative_4382_, 1);
    leanh::lean_inc_n(v_toPure_4385_, 3);
    v___f_4386_ = leanh::lean_alloc_closure(
        l_Lean_Elab_elabVisibility___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4386_, 0, v_toPure_4385_);
    leanh::lean_inc_ref(v___f_4386_);
    v___f_4387_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4387_, 0, v___f_4386_);
    v___f_4388_ = leanh::lean_alloc_closure(
        l_Lean_Elab_elabVisibility___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4388_, 0, v_toPure_4385_);
    leanh::lean_inc_ref(v___f_4388_);
    v___f_4389_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4389_, 0, v___f_4388_);
    v___f_4390_ = leanh::lean_alloc_closure(
        l_Lean_Elab_elabVisibility___redArg___lam__3___boxed as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_4390_, 0, v_vis_x3f_4381_);
    leanh::lean_closure_set(v___f_4390_, 1, v_toPure_4385_);
    leanh::lean_closure_set(v___f_4390_, 2, v_inst_4375_);
    leanh::lean_closure_set(v___f_4390_, 3, v_inst_4376_);
    leanh::lean_closure_set(v___f_4390_, 4, v_inst_4379_);
    leanh::lean_closure_set(v___f_4390_, 5, v_inst_4380_);
    leanh::lean_closure_set(v___f_4390_, 6, v_inst_4378_);
    leanh::lean_closure_set(v___f_4390_, 7, v_inst_4377_);
    leanh::lean_closure_set(v___f_4390_, 8, v_toBind_4383_);
    leanh::lean_closure_set(v___f_4390_, 9, v___f_4387_);
    leanh::lean_closure_set(v___f_4390_, 10, v___f_4386_);
    leanh::lean_closure_set(v___f_4390_, 11, v___f_4388_);
    leanh::lean_closure_set(v___f_4390_, 12, v___f_4389_);
    v___x_4391_ = leanh::lean_apply_4(
        v_toBind_4383_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_4384_,
        v___f_4390_,
    );
    return v___x_4391_;
}
pub unsafe fn l_Lean_Elab_elabVisibility(
    mut v_m_4392_: *mut leanh::LeanObject,
    mut v_inst_4393_: *mut leanh::LeanObject,
    mut v_inst_4394_: *mut leanh::LeanObject,
    mut v_inst_4395_: *mut leanh::LeanObject,
    mut v_inst_4396_: *mut leanh::LeanObject,
    mut v_inst_4397_: *mut leanh::LeanObject,
    mut v_inst_4398_: *mut leanh::LeanObject,
    mut v_vis_x3f_4399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4400_ = l_Lean_Elab_elabVisibility___redArg(
        v_inst_4393_,
        v_inst_4394_,
        v_inst_4395_,
        v_inst_4396_,
        v_inst_4397_,
        v_inst_4398_,
        v_vis_x3f_4399_,
    );
    return v___x_4400_;
}
pub unsafe fn l_Lean_Elab_RecKind_ctorIdx(mut v_x_4401_: u8) -> *mut leanh::LeanObject {
    match v_x_4401_ {
        0 => {
            let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4402_ = leanh::lean_unsigned_to_nat(0);
            return v___x_4402_;
        }
        1 => {
            let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4403_ = leanh::lean_unsigned_to_nat(1);
            return v___x_4403_;
        }
        _ => {
            let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4404_ = leanh::lean_unsigned_to_nat(2);
            return v___x_4404_;
        }
    }
}
pub unsafe fn l_Lean_Elab_RecKind_ctorIdx___boxed(
    mut v_x_4405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_4406_: u8 = 0;
    let mut v_res_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4406_ = (leanh::lean_unbox(v_x_4405_) as u8);
    v_res_4407_ = l_Lean_Elab_RecKind_ctorIdx(v_x_boxed_4406_);
    return v_res_4407_;
}
pub unsafe fn l_Lean_Elab_RecKind_toCtorIdx(mut v_x_4408_: u8) -> *mut leanh::LeanObject {
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4409_ = l_Lean_Elab_RecKind_ctorIdx(v_x_4408_);
    return v___x_4409_;
}
pub unsafe fn l_Lean_Elab_RecKind_toCtorIdx___boxed(
    mut v_x_4410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_4411_: u8 = 0;
    let mut v_res_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4411_ = (leanh::lean_unbox(v_x_4410_) as u8);
    v_res_4412_ = l_Lean_Elab_RecKind_toCtorIdx(v_x_4__boxed_4411_);
    return v_res_4412_;
}
pub unsafe fn l_Lean_Elab_RecKind_ctorElim___redArg(
    mut v_k_4413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_4413_);
    return v_k_4413_;
}
pub unsafe fn l_Lean_Elab_RecKind_ctorElim___redArg___boxed(
    mut v_k_4414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4415_ = l_Lean_Elab_RecKind_ctorElim___redArg(v_k_4414_);
    leanh::lean_dec(v_k_4414_);
    return v_res_4415_;
}
pub unsafe fn l_Lean_Elab_RecKind_ctorElim(
    mut v_motive_4416_: *mut leanh::LeanObject,
    mut v_ctorIdx_4417_: *mut leanh::LeanObject,
    mut v_t_4418_: u8,
    mut v_h_4419_: *mut leanh::LeanObject,
    mut v_k_4420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_4420_);
    return v_k_4420_;
}
pub unsafe fn l_Lean_Elab_RecKind_ctorElim___boxed(
    mut v_motive_4421_: *mut leanh::LeanObject,
    mut v_ctorIdx_4422_: *mut leanh::LeanObject,
    mut v_t_4423_: *mut leanh::LeanObject,
    mut v_h_4424_: *mut leanh::LeanObject,
    mut v_k_4425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4426_: u8 = 0;
    let mut v_res_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4426_ = (leanh::lean_unbox(v_t_4423_) as u8);
    v_res_4427_ = l_Lean_Elab_RecKind_ctorElim(
        v_motive_4421_,
        v_ctorIdx_4422_,
        v_t_boxed_4426_,
        v_h_4424_,
        v_k_4425_,
    );
    leanh::lean_dec(v_k_4425_);
    leanh::lean_dec(v_ctorIdx_4422_);
    return v_res_4427_;
}
pub unsafe fn l_Lean_Elab_RecKind_partial_elim___redArg(
    mut v_partial_4428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_partial_4428_);
    return v_partial_4428_;
}
pub unsafe fn l_Lean_Elab_RecKind_partial_elim___redArg___boxed(
    mut v_partial_4429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4430_ = l_Lean_Elab_RecKind_partial_elim___redArg(v_partial_4429_);
    leanh::lean_dec(v_partial_4429_);
    return v_res_4430_;
}
pub unsafe fn l_Lean_Elab_RecKind_partial_elim(
    mut v_motive_4431_: *mut leanh::LeanObject,
    mut v_t_4432_: u8,
    mut v_h_4433_: *mut leanh::LeanObject,
    mut v_partial_4434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_partial_4434_);
    return v_partial_4434_;
}
pub unsafe fn l_Lean_Elab_RecKind_partial_elim___boxed(
    mut v_motive_4435_: *mut leanh::LeanObject,
    mut v_t_4436_: *mut leanh::LeanObject,
    mut v_h_4437_: *mut leanh::LeanObject,
    mut v_partial_4438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4439_: u8 = 0;
    let mut v_res_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4439_ = (leanh::lean_unbox(v_t_4436_) as u8);
    v_res_4440_ = l_Lean_Elab_RecKind_partial_elim(
        v_motive_4435_,
        v_t_boxed_4439_,
        v_h_4437_,
        v_partial_4438_,
    );
    leanh::lean_dec(v_partial_4438_);
    return v_res_4440_;
}
pub unsafe fn l_Lean_Elab_RecKind_nonrec_elim___redArg(
    mut v_nonrec_4441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_nonrec_4441_);
    return v_nonrec_4441_;
}
pub unsafe fn l_Lean_Elab_RecKind_nonrec_elim___redArg___boxed(
    mut v_nonrec_4442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4443_ = l_Lean_Elab_RecKind_nonrec_elim___redArg(v_nonrec_4442_);
    leanh::lean_dec(v_nonrec_4442_);
    return v_res_4443_;
}
pub unsafe fn l_Lean_Elab_RecKind_nonrec_elim(
    mut v_motive_4444_: *mut leanh::LeanObject,
    mut v_t_4445_: u8,
    mut v_h_4446_: *mut leanh::LeanObject,
    mut v_nonrec_4447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_nonrec_4447_);
    return v_nonrec_4447_;
}
pub unsafe fn l_Lean_Elab_RecKind_nonrec_elim___boxed(
    mut v_motive_4448_: *mut leanh::LeanObject,
    mut v_t_4449_: *mut leanh::LeanObject,
    mut v_h_4450_: *mut leanh::LeanObject,
    mut v_nonrec_4451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4452_: u8 = 0;
    let mut v_res_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4452_ = (leanh::lean_unbox(v_t_4449_) as u8);
    v_res_4453_ =
        l_Lean_Elab_RecKind_nonrec_elim(v_motive_4448_, v_t_boxed_4452_, v_h_4450_, v_nonrec_4451_);
    leanh::lean_dec(v_nonrec_4451_);
    return v_res_4453_;
}
pub unsafe fn l_Lean_Elab_RecKind_default_elim___redArg(
    mut v_default_4454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_default_4454_);
    return v_default_4454_;
}
pub unsafe fn l_Lean_Elab_RecKind_default_elim___redArg___boxed(
    mut v_default_4455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4456_ = l_Lean_Elab_RecKind_default_elim___redArg(v_default_4455_);
    leanh::lean_dec(v_default_4455_);
    return v_res_4456_;
}
pub unsafe fn l_Lean_Elab_RecKind_default_elim(
    mut v_motive_4457_: *mut leanh::LeanObject,
    mut v_t_4458_: u8,
    mut v_h_4459_: *mut leanh::LeanObject,
    mut v_default_4460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_default_4460_);
    return v_default_4460_;
}
pub unsafe fn l_Lean_Elab_RecKind_default_elim___boxed(
    mut v_motive_4461_: *mut leanh::LeanObject,
    mut v_t_4462_: *mut leanh::LeanObject,
    mut v_h_4463_: *mut leanh::LeanObject,
    mut v_default_4464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4465_: u8 = 0;
    let mut v_res_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4465_ = (leanh::lean_unbox(v_t_4462_) as u8);
    v_res_4466_ = l_Lean_Elab_RecKind_default_elim(
        v_motive_4461_,
        v_t_boxed_4465_,
        v_h_4463_,
        v_default_4464_,
    );
    leanh::lean_dec(v_default_4464_);
    return v_res_4466_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedRecKind_default() -> u8 {
    let mut v___x_4467_: u8 = 0;
    v___x_4467_ = 0;
    return v___x_4467_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedRecKind() -> u8 {
    let mut v___x_4468_: u8 = 0;
    v___x_4468_ = 0;
    return v___x_4468_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_ctorIdx(mut v_x_4469_: u8) -> *mut leanh::LeanObject {
    match v_x_4469_ {
        0 => {
            let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4470_ = leanh::lean_unsigned_to_nat(0);
            return v___x_4470_;
        }
        1 => {
            let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4471_ = leanh::lean_unsigned_to_nat(1);
            return v___x_4471_;
        }
        _ => {
            let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4472_ = leanh::lean_unsigned_to_nat(2);
            return v___x_4472_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ComputeKind_ctorIdx___boxed(
    mut v_x_4473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_4474_: u8 = 0;
    let mut v_res_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4474_ = (leanh::lean_unbox(v_x_4473_) as u8);
    v_res_4475_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_boxed_4474_);
    return v_res_4475_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_toCtorIdx(
    mut v_x_4476_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4477_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_4476_);
    return v___x_4477_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_toCtorIdx___boxed(
    mut v_x_4478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_4479_: u8 = 0;
    let mut v_res_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4479_ = (leanh::lean_unbox(v_x_4478_) as u8);
    v_res_4480_ = l_Lean_Elab_ComputeKind_toCtorIdx(v_x_4__boxed_4479_);
    return v_res_4480_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_ctorElim___redArg(
    mut v_k_4481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_4481_);
    return v_k_4481_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_ctorElim___redArg___boxed(
    mut v_k_4482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4483_ = l_Lean_Elab_ComputeKind_ctorElim___redArg(v_k_4482_);
    leanh::lean_dec(v_k_4482_);
    return v_res_4483_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_ctorElim(
    mut v_motive_4484_: *mut leanh::LeanObject,
    mut v_ctorIdx_4485_: *mut leanh::LeanObject,
    mut v_t_4486_: u8,
    mut v_h_4487_: *mut leanh::LeanObject,
    mut v_k_4488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_4488_);
    return v_k_4488_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_ctorElim___boxed(
    mut v_motive_4489_: *mut leanh::LeanObject,
    mut v_ctorIdx_4490_: *mut leanh::LeanObject,
    mut v_t_4491_: *mut leanh::LeanObject,
    mut v_h_4492_: *mut leanh::LeanObject,
    mut v_k_4493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4494_: u8 = 0;
    let mut v_res_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4494_ = (leanh::lean_unbox(v_t_4491_) as u8);
    v_res_4495_ = l_Lean_Elab_ComputeKind_ctorElim(
        v_motive_4489_,
        v_ctorIdx_4490_,
        v_t_boxed_4494_,
        v_h_4492_,
        v_k_4493_,
    );
    leanh::lean_dec(v_k_4493_);
    leanh::lean_dec(v_ctorIdx_4490_);
    return v_res_4495_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_regular_elim___redArg(
    mut v_regular_4496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_regular_4496_);
    return v_regular_4496_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_regular_elim___redArg___boxed(
    mut v_regular_4497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4498_ = l_Lean_Elab_ComputeKind_regular_elim___redArg(v_regular_4497_);
    leanh::lean_dec(v_regular_4497_);
    return v_res_4498_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_regular_elim(
    mut v_motive_4499_: *mut leanh::LeanObject,
    mut v_t_4500_: u8,
    mut v_h_4501_: *mut leanh::LeanObject,
    mut v_regular_4502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_regular_4502_);
    return v_regular_4502_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_regular_elim___boxed(
    mut v_motive_4503_: *mut leanh::LeanObject,
    mut v_t_4504_: *mut leanh::LeanObject,
    mut v_h_4505_: *mut leanh::LeanObject,
    mut v_regular_4506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4507_: u8 = 0;
    let mut v_res_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4507_ = (leanh::lean_unbox(v_t_4504_) as u8);
    v_res_4508_ = l_Lean_Elab_ComputeKind_regular_elim(
        v_motive_4503_,
        v_t_boxed_4507_,
        v_h_4505_,
        v_regular_4506_,
    );
    leanh::lean_dec(v_regular_4506_);
    return v_res_4508_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_meta_elim___redArg(
    mut v_meta_4509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_meta_4509_);
    return v_meta_4509_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_meta_elim___redArg___boxed(
    mut v_meta_4510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4511_ = l_Lean_Elab_ComputeKind_meta_elim___redArg(v_meta_4510_);
    leanh::lean_dec(v_meta_4510_);
    return v_res_4511_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_meta_elim(
    mut v_motive_4512_: *mut leanh::LeanObject,
    mut v_t_4513_: u8,
    mut v_h_4514_: *mut leanh::LeanObject,
    mut v_meta_4515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_meta_4515_);
    return v_meta_4515_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_meta_elim___boxed(
    mut v_motive_4516_: *mut leanh::LeanObject,
    mut v_t_4517_: *mut leanh::LeanObject,
    mut v_h_4518_: *mut leanh::LeanObject,
    mut v_meta_4519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4520_: u8 = 0;
    let mut v_res_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4520_ = (leanh::lean_unbox(v_t_4517_) as u8);
    v_res_4521_ =
        l_Lean_Elab_ComputeKind_meta_elim(v_motive_4516_, v_t_boxed_4520_, v_h_4518_, v_meta_4519_);
    leanh::lean_dec(v_meta_4519_);
    return v_res_4521_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(
    mut v_noncomputable_4522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_noncomputable_4522_);
    return v_noncomputable_4522_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_noncomputable_elim___redArg___boxed(
    mut v_noncomputable_4523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4524_ = l_Lean_Elab_ComputeKind_noncomputable_elim___redArg(v_noncomputable_4523_);
    leanh::lean_dec(v_noncomputable_4523_);
    return v_res_4524_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_noncomputable_elim(
    mut v_motive_4525_: *mut leanh::LeanObject,
    mut v_t_4526_: u8,
    mut v_h_4527_: *mut leanh::LeanObject,
    mut v_noncomputable_4528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_noncomputable_4528_);
    return v_noncomputable_4528_;
}
pub unsafe fn l_Lean_Elab_ComputeKind_noncomputable_elim___boxed(
    mut v_motive_4529_: *mut leanh::LeanObject,
    mut v_t_4530_: *mut leanh::LeanObject,
    mut v_h_4531_: *mut leanh::LeanObject,
    mut v_noncomputable_4532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4533_: u8 = 0;
    let mut v_res_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4533_ = (leanh::lean_unbox(v_t_4530_) as u8);
    v_res_4534_ = l_Lean_Elab_ComputeKind_noncomputable_elim(
        v_motive_4529_,
        v_t_boxed_4533_,
        v_h_4531_,
        v_noncomputable_4532_,
    );
    leanh::lean_dec(v_noncomputable_4532_);
    return v_res_4534_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedComputeKind_default() -> u8 {
    let mut v___x_4535_: u8 = 0;
    v___x_4535_ = 0;
    return v___x_4535_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedComputeKind() -> u8 {
    let mut v___x_4536_: u8 = 0;
    v___x_4536_ = 0;
    return v___x_4536_;
}
pub unsafe fn l_Lean_Elab_instBEqComputeKind_beq(mut v_x_4537_: u8, mut v_y_4538_: u8) -> u8 {
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: u8 = 0;
    v___x_4539_ = l_Lean_Elab_ComputeKind_ctorIdx(v_x_4537_);
    v___x_4540_ = l_Lean_Elab_ComputeKind_ctorIdx(v_y_4538_);
    v___x_4541_ = lean_nat_dec_eq(v___x_4539_, v___x_4540_);
    leanh::lean_dec(v___x_4540_);
    leanh::lean_dec(v___x_4539_);
    return v___x_4541_;
}
pub unsafe fn l_Lean_Elab_instBEqComputeKind_beq___boxed(
    mut v_x_4542_: *mut leanh::LeanObject,
    mut v_y_4543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_4544_: u8 = 0;
    let mut v_y_18__boxed_4545_: u8 = 0;
    let mut v_res_4546_: u8 = 0;
    let mut v_r_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_4544_ = (leanh::lean_unbox(v_x_4542_) as u8);
    v_y_18__boxed_4545_ = (leanh::lean_unbox(v_y_4543_) as u8);
    v_res_4546_ = l_Lean_Elab_instBEqComputeKind_beq(v_x_17__boxed_4544_, v_y_18__boxed_4545_);
    v_r_4547_ = leanh::lean_box((v_res_4546_) as usize);
    return v_r_4547_;
}
pub unsafe fn _init_l_Lean_Elab_instReprComputeKind_repr___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4559_ = leanh::lean_unsigned_to_nat(2);
    v___x_4560_ = lean_nat_to_int(v___x_4559_);
    return v___x_4560_;
}
pub unsafe fn _init_l_Lean_Elab_instReprComputeKind_repr___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4561_ = leanh::lean_unsigned_to_nat(1);
    v___x_4562_ = lean_nat_to_int(v___x_4561_);
    return v___x_4562_;
}
pub unsafe fn l_Lean_Elab_instReprComputeKind_repr(
    mut v_x_4563_: u8,
    mut v_prec_4564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: u8 = 0;
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: u8 = 0;
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: u8 = 0;
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: u8 = 0;
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: u8 = 0;
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: u8 = 0;
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_4563_ {
                0 => {
                    v___x_4586_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_4587_ = lean_nat_dec_le(v___x_4586_, v_prec_4564_);
                    if v___x_4587_ == 0 {
                        v___x_4588_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprComputeKind_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprComputeKind_repr___closed__6_once
                            ),
                            _init_l_Lean_Elab_instReprComputeKind_repr___closed__6,
                        );
                        v___y_4566_ = v___x_4588_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4589_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprComputeKind_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprComputeKind_repr___closed__7_once
                            ),
                            _init_l_Lean_Elab_instReprComputeKind_repr___closed__7,
                        );
                        v___y_4566_ = v___x_4589_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_4590_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_4591_ = lean_nat_dec_le(v___x_4590_, v_prec_4564_);
                    if v___x_4591_ == 0 {
                        v___x_4592_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprComputeKind_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprComputeKind_repr___closed__6_once
                            ),
                            _init_l_Lean_Elab_instReprComputeKind_repr___closed__6,
                        );
                        v___y_4573_ = v___x_4592_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4593_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprComputeKind_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprComputeKind_repr___closed__7_once
                            ),
                            _init_l_Lean_Elab_instReprComputeKind_repr___closed__7,
                        );
                        v___y_4573_ = v___x_4593_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_4594_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_4595_ = lean_nat_dec_le(v___x_4594_, v_prec_4564_);
                    if v___x_4595_ == 0 {
                        v___x_4596_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprComputeKind_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprComputeKind_repr___closed__6_once
                            ),
                            _init_l_Lean_Elab_instReprComputeKind_repr___closed__6,
                        );
                        v___y_4580_ = v___x_4596_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4597_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprComputeKind_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprComputeKind_repr___closed__7_once
                            ),
                            _init_l_Lean_Elab_instReprComputeKind_repr___closed__7,
                        );
                        v___y_4580_ = v___x_4597_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4567_ = l_Lean_Elab_instReprComputeKind_repr___closed__1;
                leanh::lean_inc(v___y_4566_);
                v___x_4568_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4568_, 0, v___y_4566_);
                leanh::lean_ctor_set(v___x_4568_, 1, v___x_4567_);
                v___x_4569_ = 0;
                v___x_4570_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4570_, 0, v___x_4568_);
                leanh::lean_ctor_set_uint8(
                    v___x_4570_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4569_,
                );
                v___x_4571_ = l_Repr_addAppParen(v___x_4570_, v_prec_4564_);
                return v___x_4571_;
            }
            2 => {
                v___x_4574_ = l_Lean_Elab_instReprComputeKind_repr___closed__3;
                leanh::lean_inc(v___y_4573_);
                v___x_4575_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4575_, 0, v___y_4573_);
                leanh::lean_ctor_set(v___x_4575_, 1, v___x_4574_);
                v___x_4576_ = 0;
                v___x_4577_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4577_, 0, v___x_4575_);
                leanh::lean_ctor_set_uint8(
                    v___x_4577_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4576_,
                );
                v___x_4578_ = l_Repr_addAppParen(v___x_4577_, v_prec_4564_);
                return v___x_4578_;
            }
            3 => {
                v___x_4581_ = l_Lean_Elab_instReprComputeKind_repr___closed__5;
                leanh::lean_inc(v___y_4580_);
                v___x_4582_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4582_, 0, v___y_4580_);
                leanh::lean_ctor_set(v___x_4582_, 1, v___x_4581_);
                v___x_4583_ = 0;
                v___x_4584_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4584_, 0, v___x_4582_);
                leanh::lean_ctor_set_uint8(
                    v___x_4584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4583_,
                );
                v___x_4585_ = l_Repr_addAppParen(v___x_4584_, v_prec_4564_);
                return v___x_4585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_instReprComputeKind_repr___boxed(
    mut v_x_4598_: *mut leanh::LeanObject,
    mut v_prec_4599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_177__boxed_4600_: u8 = 0;
    let mut v_res_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_177__boxed_4600_ = (leanh::lean_unbox(v_x_4598_) as u8);
    v_res_4601_ = l_Lean_Elab_instReprComputeKind_repr(v_x_177__boxed_4600_, v_prec_4599_);
    leanh::lean_dec(v_prec_4599_);
    return v_res_4601_;
}
pub unsafe fn l_Lean_Elab_Modifiers_isPrivate(mut v_m_4616_: *mut leanh::LeanObject) -> u8 {
    let mut v_visibility_4617_: u8 = 0;
    let mut v___x_4618_: u8 = 0;
    v_visibility_4617_ = leanh::lean_ctor_get_uint8(
        v_m_4616_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v___x_4618_ = l_Lean_Elab_Visibility_isPrivate(v_visibility_4617_);
    return v___x_4618_;
}
pub unsafe fn l_Lean_Elab_Modifiers_isPrivate___boxed(
    mut v_m_4619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4620_: u8 = 0;
    let mut v_r_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4620_ = l_Lean_Elab_Modifiers_isPrivate(v_m_4619_);
    leanh::lean_dec_ref(v_m_4619_);
    v_r_4621_ = leanh::lean_box((v_res_4620_) as usize);
    return v_r_4621_;
}
pub unsafe fn l_Lean_Elab_Modifiers_isPublic(mut v_m_4622_: *mut leanh::LeanObject) -> u8 {
    let mut v_visibility_4623_: u8 = 0;
    let mut v___x_4624_: u8 = 0;
    v_visibility_4623_ = leanh::lean_ctor_get_uint8(
        v_m_4622_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v___x_4624_ = l_Lean_Elab_Visibility_isPublic(v_visibility_4623_);
    return v___x_4624_;
}
pub unsafe fn l_Lean_Elab_Modifiers_isPublic___boxed(
    mut v_m_4625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4626_: u8 = 0;
    let mut v_r_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4626_ = l_Lean_Elab_Modifiers_isPublic(v_m_4625_);
    leanh::lean_dec_ref(v_m_4625_);
    v_r_4627_ = leanh::lean_box((v_res_4626_) as usize);
    return v_r_4627_;
}
pub unsafe fn l_Lean_Elab_Modifiers_isInferredPublic(
    mut v_env_4628_: *mut leanh::LeanObject,
    mut v_m_4629_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_visibility_4630_: u8 = 0;
    let mut v___x_4631_: u8 = 0;
    v_visibility_4630_ = leanh::lean_ctor_get_uint8(
        v_m_4629_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v___x_4631_ = l_Lean_Elab_Visibility_isInferredPublic(v_env_4628_, v_visibility_4630_);
    return v___x_4631_;
}
pub unsafe fn l_Lean_Elab_Modifiers_isInferredPublic___boxed(
    mut v_env_4632_: *mut leanh::LeanObject,
    mut v_m_4633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4634_: u8 = 0;
    let mut v_r_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4634_ = l_Lean_Elab_Modifiers_isInferredPublic(v_env_4632_, v_m_4633_);
    leanh::lean_dec_ref(v_m_4633_);
    leanh::lean_dec_ref(v_env_4632_);
    v_r_4635_ = leanh::lean_box((v_res_4634_) as usize);
    return v_r_4635_;
}
pub unsafe fn l_Lean_Elab_Modifiers_isPartial(mut v_x_4636_: *mut leanh::LeanObject) -> u8 {
    let mut v_recKind_4637_: u8 = 0;
    v_recKind_4637_ = leanh::lean_ctor_get_uint8(
        v_x_4636_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3) as u32,
    );
    if v_recKind_4637_ == 0 {
        let mut v___x_4638_: u8 = 0;
        v___x_4638_ = 1;
        return v___x_4638_;
    } else {
        let mut v___x_4639_: u8 = 0;
        v___x_4639_ = 0;
        return v___x_4639_;
    }
}
pub unsafe fn l_Lean_Elab_Modifiers_isPartial___boxed(
    mut v_x_4640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4641_: u8 = 0;
    let mut v_r_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4641_ = l_Lean_Elab_Modifiers_isPartial(v_x_4640_);
    leanh::lean_dec_ref(v_x_4640_);
    v_r_4642_ = leanh::lean_box((v_res_4641_) as usize);
    return v_r_4642_;
}
pub unsafe fn l_Lean_Elab_Modifiers_isNonrec(mut v_x_4643_: *mut leanh::LeanObject) -> u8 {
    let mut v_recKind_4644_: u8 = 0;
    v_recKind_4644_ = leanh::lean_ctor_get_uint8(
        v_x_4643_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3) as u32,
    );
    if v_recKind_4644_ == 1 {
        let mut v___x_4645_: u8 = 0;
        v___x_4645_ = 1;
        return v___x_4645_;
    } else {
        let mut v___x_4646_: u8 = 0;
        v___x_4646_ = 0;
        return v___x_4646_;
    }
}
pub unsafe fn l_Lean_Elab_Modifiers_isNonrec___boxed(
    mut v_x_4647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4648_: u8 = 0;
    let mut v_r_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4648_ = l_Lean_Elab_Modifiers_isNonrec(v_x_4647_);
    leanh::lean_dec_ref(v_x_4647_);
    v_r_4649_ = leanh::lean_box((v_res_4648_) as usize);
    return v_r_4649_;
}
pub unsafe fn l_Lean_Elab_Modifiers_isMeta(mut v_m_4650_: *mut leanh::LeanObject) -> u8 {
    let mut v_computeKind_4651_: u8 = 0;
    v_computeKind_4651_ = leanh::lean_ctor_get_uint8(
        v_m_4650_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
    );
    if v_computeKind_4651_ == 1 {
        let mut v___x_4652_: u8 = 0;
        v___x_4652_ = 1;
        return v___x_4652_;
    } else {
        let mut v___x_4653_: u8 = 0;
        v___x_4653_ = 0;
        return v___x_4653_;
    }
}
pub unsafe fn l_Lean_Elab_Modifiers_isMeta___boxed(
    mut v_m_4654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4655_: u8 = 0;
    let mut v_r_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4655_ = l_Lean_Elab_Modifiers_isMeta(v_m_4654_);
    leanh::lean_dec_ref(v_m_4654_);
    v_r_4656_ = leanh::lean_box((v_res_4655_) as usize);
    return v_r_4656_;
}
pub unsafe fn l_Lean_Elab_Modifiers_isNoncomputable(
    mut v_m_4657_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_computeKind_4658_: u8 = 0;
    v_computeKind_4658_ = leanh::lean_ctor_get_uint8(
        v_m_4657_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
    );
    if v_computeKind_4658_ == 2 {
        let mut v___x_4659_: u8 = 0;
        v___x_4659_ = 1;
        return v___x_4659_;
    } else {
        let mut v___x_4660_: u8 = 0;
        v___x_4660_ = 0;
        return v___x_4660_;
    }
}
pub unsafe fn l_Lean_Elab_Modifiers_isNoncomputable___boxed(
    mut v_m_4661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4662_: u8 = 0;
    let mut v_r_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4662_ = l_Lean_Elab_Modifiers_isNoncomputable(v_m_4661_);
    leanh::lean_dec_ref(v_m_4661_);
    v_r_4663_ = leanh::lean_box((v_res_4662_) as usize);
    return v_r_4663_;
}
pub unsafe fn l_Lean_Elab_Modifiers_addAttr(
    mut v_modifiers_4664_: *mut leanh::LeanObject,
    mut v_attr_4665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stx_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visibility_4668_: u8 = 0;
    let mut v_isProtected_4669_: u8 = 0;
    let mut v_computeKind_4670_: u8 = 0;
    let mut v_recKind_4671_: u8 = 0;
    let mut v_isUnsafe_4672_: u8 = 0;
    let mut v_attrs_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4676_: u8 = 0;
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stx_4666_ = leanh::lean_ctor_get(v_modifiers_4664_, 0);
                v_docString_x3f_4667_ = leanh::lean_ctor_get(v_modifiers_4664_, 1);
                v_visibility_4668_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4664_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_isProtected_4669_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4664_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_computeKind_4670_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4664_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                );
                v_recKind_4671_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4664_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3) as u32,
                );
                v_isUnsafe_4672_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4664_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4) as u32,
                );
                v_attrs_4673_ = leanh::lean_ctor_get(v_modifiers_4664_, 2);
                v_isSharedCheck_4681_ = (!leanh::lean_is_exclusive(v_modifiers_4664_)) as u8;
                if v_isSharedCheck_4681_ == 0 {
                    v___x_4675_ = v_modifiers_4664_;
                    v_isShared_4676_ = v_isSharedCheck_4681_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_attrs_4673_);
                    leanh::lean_inc(v_docString_x3f_4667_);
                    leanh::lean_inc(v_stx_4666_);
                    leanh::lean_dec(v_modifiers_4664_);
                    v___x_4675_ = leanh::lean_box(0);
                    v_isShared_4676_ = v_isSharedCheck_4681_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4677_ = lean_array_push(v_attrs_4673_, v_attr_4665_);
                if v_isShared_4676_ == 0 {
                    leanh::lean_ctor_set(v___x_4675_, 2, v___x_4677_);
                    v___x_4679_ = v___x_4675_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4680_ = leanh::lean_alloc_ctor(0, 3, (5) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_stx_4666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4680_, 1, v_docString_x3f_4667_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4680_, 2, v___x_4677_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4680_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_visibility_4668_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4680_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                        v_isProtected_4669_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4680_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                        v_computeKind_4670_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4680_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3) as u32,
                        v_recKind_4671_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4680_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4) as u32,
                        v_isUnsafe_4672_,
                    );
                    v___x_4679_ = v_reuseFailAlloc_4680_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Modifiers_addFirstAttr(
    mut v_modifiers_4682_: *mut leanh::LeanObject,
    mut v_attr_4683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stx_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visibility_4686_: u8 = 0;
    let mut v_isProtected_4687_: u8 = 0;
    let mut v_computeKind_4688_: u8 = 0;
    let mut v_recKind_4689_: u8 = 0;
    let mut v_isUnsafe_4690_: u8 = 0;
    let mut v_attrs_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4694_: u8 = 0;
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stx_4684_ = leanh::lean_ctor_get(v_modifiers_4682_, 0);
                v_docString_x3f_4685_ = leanh::lean_ctor_get(v_modifiers_4682_, 1);
                v_visibility_4686_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4682_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_isProtected_4687_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4682_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_computeKind_4688_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4682_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                );
                v_recKind_4689_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4682_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3) as u32,
                );
                v_isUnsafe_4690_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4682_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4) as u32,
                );
                v_attrs_4691_ = leanh::lean_ctor_get(v_modifiers_4682_, 2);
                v_isSharedCheck_4702_ = (!leanh::lean_is_exclusive(v_modifiers_4682_)) as u8;
                if v_isSharedCheck_4702_ == 0 {
                    v___x_4693_ = v_modifiers_4682_;
                    v_isShared_4694_ = v_isSharedCheck_4702_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_attrs_4691_);
                    leanh::lean_inc(v_docString_x3f_4685_);
                    leanh::lean_inc(v_stx_4684_);
                    leanh::lean_dec(v_modifiers_4682_);
                    v___x_4693_ = leanh::lean_box(0);
                    v_isShared_4694_ = v_isSharedCheck_4702_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4695_ = leanh::lean_unsigned_to_nat(1);
                v___x_4696_ = lean_mk_empty_array_with_capacity(v___x_4695_);
                v___x_4697_ = lean_array_push(v___x_4696_, v_attr_4683_);
                v___x_4698_ = l_Array_append___redArg(v___x_4697_, v_attrs_4691_);
                leanh::lean_dec_ref(v_attrs_4691_);
                if v_isShared_4694_ == 0 {
                    leanh::lean_ctor_set(v___x_4693_, 2, v___x_4698_);
                    v___x_4700_ = v___x_4693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4701_ = leanh::lean_alloc_ctor(0, 3, (5) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_stx_4684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4701_, 1, v_docString_x3f_4685_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4701_, 2, v___x_4698_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4701_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_visibility_4686_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4701_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                        v_isProtected_4687_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4701_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                        v_computeKind_4688_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4701_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3) as u32,
                        v_recKind_4689_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4701_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4) as u32,
                        v_isUnsafe_4690_,
                    );
                    v___x_4700_ = v_reuseFailAlloc_4701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(
    mut v_p_4703_: *mut leanh::LeanObject,
    mut v_as_4704_: *mut leanh::LeanObject,
    mut v_i_4705_: usize,
    mut v_stop_4706_: usize,
    mut v_b_4707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: usize = 0;
    let mut v___x_4711_: usize = 0;
    let mut v___x_4713_: u8 = 0;
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: u8 = 0;
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4713_ = lean_usize_dec_eq(v_i_4705_, v_stop_4706_);
                if v___x_4713_ == 0 {
                    v___x_4714_ = lean_array_uget_borrowed(v_as_4704_, v_i_4705_);
                    leanh::lean_inc_ref(v_p_4703_);
                    leanh::lean_inc(v___x_4714_);
                    v___x_4715_ = leanh::lean_apply_1(v_p_4703_, v___x_4714_);
                    v___x_4716_ = (leanh::lean_unbox(v___x_4715_) as u8);
                    if v___x_4716_ == 0 {
                        v___y_4709_ = v_b_4707_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_4714_);
                        v___x_4717_ = lean_array_push(v_b_4707_, v___x_4714_);
                        v___y_4709_ = v___x_4717_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_p_4703_);
                    return v_b_4707_;
                }
            }
            1 => {
                v___x_4710_ = 1usize;
                v___x_4711_ = lean_usize_add(v_i_4705_, v___x_4710_);
                v_i_4705_ = v___x_4711_;
                v_b_4707_ = v___y_4709_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0___boxed(
    mut v_p_4718_: *mut leanh::LeanObject,
    mut v_as_4719_: *mut leanh::LeanObject,
    mut v_i_4720_: *mut leanh::LeanObject,
    mut v_stop_4721_: *mut leanh::LeanObject,
    mut v_b_4722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4723_: usize = 0;
    let mut v_stop_boxed_4724_: usize = 0;
    let mut v_res_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4723_ = leanh::lean_unbox_usize(v_i_4720_);
    leanh::lean_dec(v_i_4720_);
    v_stop_boxed_4724_ = leanh::lean_unbox_usize(v_stop_4721_);
    leanh::lean_dec(v_stop_4721_);
    v_res_4725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_4718_, v_as_4719_, v_i_boxed_4723_, v_stop_boxed_4724_, v_b_4722_);
    leanh::lean_dec_ref(v_as_4719_);
    return v_res_4725_;
}
pub unsafe fn l_Lean_Elab_Modifiers_filterAttrs(
    mut v_modifiers_4726_: *mut leanh::LeanObject,
    mut v_p_4727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stx_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visibility_4730_: u8 = 0;
    let mut v_isProtected_4731_: u8 = 0;
    let mut v_computeKind_4732_: u8 = 0;
    let mut v_recKind_4733_: u8 = 0;
    let mut v_isUnsafe_4734_: u8 = 0;
    let mut v_attrs_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4738_: u8 = 0;
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: u8 = 0;
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: u8 = 0;
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: usize = 0;
    let mut v___x_4751_: usize = 0;
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: usize = 0;
    let mut v___x_4757_: usize = 0;
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stx_4728_ = leanh::lean_ctor_get(v_modifiers_4726_, 0);
                v_docString_x3f_4729_ = leanh::lean_ctor_get(v_modifiers_4726_, 1);
                v_visibility_4730_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4726_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_isProtected_4731_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4726_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_computeKind_4732_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4726_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                );
                v_recKind_4733_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4726_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3) as u32,
                );
                v_isUnsafe_4734_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_4726_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4) as u32,
                );
                v_attrs_4735_ = leanh::lean_ctor_get(v_modifiers_4726_, 2);
                v_isSharedCheck_4762_ = (!leanh::lean_is_exclusive(v_modifiers_4726_)) as u8;
                if v_isSharedCheck_4762_ == 0 {
                    v___x_4737_ = v_modifiers_4726_;
                    v_isShared_4738_ = v_isSharedCheck_4762_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_attrs_4735_);
                    leanh::lean_inc(v_docString_x3f_4729_);
                    leanh::lean_inc(v_stx_4728_);
                    leanh::lean_dec(v_modifiers_4726_);
                    v___x_4737_ = leanh::lean_box(0);
                    v_isShared_4738_ = v_isSharedCheck_4762_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4739_ = leanh::lean_unsigned_to_nat(0);
                v___x_4740_ = lean_array_get_size(v_attrs_4735_);
                v___x_4741_ = l_Lean_Elab_instInhabitedModifiers_default___closed__0;
                v___x_4742_ = lean_nat_dec_lt(v___x_4739_, v___x_4740_);
                if v___x_4742_ == 0 {
                    leanh::lean_dec_ref(v_attrs_4735_);
                    leanh::lean_dec_ref(v_p_4727_);
                    if v_isShared_4738_ == 0 {
                        leanh::lean_ctor_set(v___x_4737_, 2, v___x_4741_);
                        v___x_4744_ = v___x_4737_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4745_ = leanh::lean_alloc_ctor(0, 3, (5) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_stx_4728_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_4745_,
                            1,
                            v_docString_x3f_4729_,
                        );
                        leanh::lean_ctor_set(v_reuseFailAlloc_4745_, 2, v___x_4741_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4745_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                            v_visibility_4730_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4745_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                            v_isProtected_4731_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4745_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                            v_computeKind_4732_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4745_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3) as u32,
                            v_recKind_4733_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4745_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4) as u32,
                            v_isUnsafe_4734_,
                        );
                        v___x_4744_ = v_reuseFailAlloc_4745_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4746_ = lean_nat_dec_le(v___x_4740_, v___x_4740_);
                    if v___x_4746_ == 0 {
                        if v___x_4742_ == 0 {
                            leanh::lean_dec_ref(v_attrs_4735_);
                            leanh::lean_dec_ref(v_p_4727_);
                            if v_isShared_4738_ == 0 {
                                leanh::lean_ctor_set(v___x_4737_, 2, v___x_4741_);
                                v___x_4748_ = v___x_4737_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4749_ =
                                    leanh::lean_alloc_ctor(0, 3, (5) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_stx_4728_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4749_,
                                    1,
                                    v_docString_x3f_4729_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 2, v___x_4741_);
                                leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_4749_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3)
                                        as u32,
                                    v_visibility_4730_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_4749_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1)
                                        as u32,
                                    v_isProtected_4731_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_4749_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2)
                                        as u32,
                                    v_computeKind_4732_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_4749_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3)
                                        as u32,
                                    v_recKind_4733_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_4749_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4)
                                        as u32,
                                    v_isUnsafe_4734_,
                                );
                                v___x_4748_ = v_reuseFailAlloc_4749_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_4750_ = 0usize;
                            v___x_4751_ = lean_usize_of_nat(v___x_4740_);
                            v___x_4752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_4727_, v_attrs_4735_, v___x_4750_, v___x_4751_, v___x_4741_);
                            leanh::lean_dec_ref(v_attrs_4735_);
                            if v_isShared_4738_ == 0 {
                                leanh::lean_ctor_set(v___x_4737_, 2, v___x_4752_);
                                v___x_4754_ = v___x_4737_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_4755_ =
                                    leanh::lean_alloc_ctor(0, 3, (5) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_stx_4728_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4755_,
                                    1,
                                    v_docString_x3f_4729_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_4755_, 2, v___x_4752_);
                                leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_4755_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3)
                                        as u32,
                                    v_visibility_4730_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_4755_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1)
                                        as u32,
                                    v_isProtected_4731_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_4755_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2)
                                        as u32,
                                    v_computeKind_4732_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_4755_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3)
                                        as u32,
                                    v_recKind_4733_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_4755_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4)
                                        as u32,
                                    v_isUnsafe_4734_,
                                );
                                v___x_4754_ = v_reuseFailAlloc_4755_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___x_4756_ = 0usize;
                        v___x_4757_ = lean_usize_of_nat(v___x_4740_);
                        v___x_4758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Modifiers_filterAttrs_spec__0(v_p_4727_, v_attrs_4735_, v___x_4756_, v___x_4757_, v___x_4741_);
                        leanh::lean_dec_ref(v_attrs_4735_);
                        if v_isShared_4738_ == 0 {
                            leanh::lean_ctor_set(v___x_4737_, 2, v___x_4758_);
                            v___x_4760_ = v___x_4737_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4761_ =
                                leanh::lean_alloc_ctor(0, 3, (5) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_stx_4728_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4761_,
                                1,
                                v_docString_x3f_4729_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_4761_, 2, v___x_4758_);
                            leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_4761_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                                v_visibility_4730_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_4761_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1)
                                    as u32,
                                v_isProtected_4731_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_4761_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2)
                                    as u32,
                                v_computeKind_4732_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_4761_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3)
                                    as u32,
                                v_recKind_4733_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_4761_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4)
                                    as u32,
                                v_isUnsafe_4734_,
                            );
                            v___x_4760_ = v_reuseFailAlloc_4761_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4744_;
            }
            3 => {
                return v___x_4748_;
            }
            4 => {
                return v___x_4754_;
            }
            5 => {
                return v___x_4760_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(
    mut v_p_4763_: *mut leanh::LeanObject,
    mut v_as_4764_: *mut leanh::LeanObject,
    mut v_i_4765_: usize,
    mut v_stop_4766_: usize,
) -> u8 {
    let mut v___x_4767_: u8 = 0;
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: u8 = 0;
    let mut v___x_4771_: usize = 0;
    let mut v___x_4772_: usize = 0;
    let mut v___x_4774_: u8 = 0;
    let mut v___x_4775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4767_ = lean_usize_dec_eq(v_i_4765_, v_stop_4766_);
                if v___x_4767_ == 0 {
                    v___x_4768_ = lean_array_uget_borrowed(v_as_4764_, v_i_4765_);
                    leanh::lean_inc_ref(v_p_4763_);
                    leanh::lean_inc(v___x_4768_);
                    v___x_4769_ = leanh::lean_apply_1(v_p_4763_, v___x_4768_);
                    v___x_4770_ = (leanh::lean_unbox(v___x_4769_) as u8);
                    if v___x_4770_ == 0 {
                        v___x_4771_ = 1usize;
                        v___x_4772_ = lean_usize_add(v_i_4765_, v___x_4771_);
                        v_i_4765_ = v___x_4772_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_p_4763_);
                        v___x_4774_ = (leanh::lean_unbox(v___x_4769_) as u8);
                        return v___x_4774_;
                    }
                } else {
                    leanh::lean_dec_ref(v_p_4763_);
                    v___x_4775_ = 0;
                    return v___x_4775_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0___boxed(
    mut v_p_4776_: *mut leanh::LeanObject,
    mut v_as_4777_: *mut leanh::LeanObject,
    mut v_i_4778_: *mut leanh::LeanObject,
    mut v_stop_4779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4780_: usize = 0;
    let mut v_stop_boxed_4781_: usize = 0;
    let mut v_res_4782_: u8 = 0;
    let mut v_r_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4780_ = leanh::lean_unbox_usize(v_i_4778_);
    leanh::lean_dec(v_i_4778_);
    v_stop_boxed_4781_ = leanh::lean_unbox_usize(v_stop_4779_);
    leanh::lean_dec(v_stop_4779_);
    v_res_4782_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_4776_, v_as_4777_, v_i_boxed_4780_, v_stop_boxed_4781_);
    leanh::lean_dec_ref(v_as_4777_);
    v_r_4783_ = leanh::lean_box((v_res_4782_) as usize);
    return v_r_4783_;
}
pub unsafe fn l_Lean_Elab_Modifiers_anyAttr(
    mut v_modifiers_4784_: *mut leanh::LeanObject,
    mut v_p_4785_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_attrs_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: u8 = 0;
    v_attrs_4786_ = leanh::lean_ctor_get(v_modifiers_4784_, 2);
    v___x_4787_ = leanh::lean_unsigned_to_nat(0);
    v___x_4788_ = lean_array_get_size(v_attrs_4786_);
    v___x_4789_ = lean_nat_dec_lt(v___x_4787_, v___x_4788_);
    if v___x_4789_ == 0 {
        leanh::lean_dec_ref(v_p_4785_);
        return v___x_4789_;
    } else {
        if v___x_4789_ == 0 {
            leanh::lean_dec_ref(v_p_4785_);
            return v___x_4789_;
        } else {
            let mut v___x_4790_: usize = 0;
            let mut v___x_4791_: usize = 0;
            let mut v___x_4792_: u8 = 0;
            v___x_4790_ = 0usize;
            v___x_4791_ = lean_usize_of_nat(v___x_4788_);
            v___x_4792_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Modifiers_anyAttr_spec__0(v_p_4785_, v_attrs_4786_, v___x_4790_, v___x_4791_);
            return v___x_4792_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Modifiers_anyAttr___boxed(
    mut v_modifiers_4793_: *mut leanh::LeanObject,
    mut v_p_4794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4795_: u8 = 0;
    let mut v_r_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4795_ = l_Lean_Elab_Modifiers_anyAttr(v_modifiers_4793_, v_p_4794_);
    leanh::lean_dec_ref(v_modifiers_4793_);
    v_r_4796_ = leanh::lean_box((v_res_4795_) as usize);
    return v_r_4796_;
}
pub unsafe fn _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4799_ = l_Lean_Elab_instToFormatModifiers___lam__0___closed__0;
    v___x_4800_ = lean_string_length(v___x_4799_);
    return v___x_4800_;
}
pub unsafe fn _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4801_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instToFormatModifiers___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_instToFormatModifiers___lam__0___closed__2_once),
        _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__2,
    );
    v___x_4802_ = lean_nat_to_int(v___x_4801_);
    return v___x_4802_;
}
pub unsafe fn l_Lean_Elab_instToFormatModifiers___lam__0(
    mut v_attr_4809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_4810_: u8 = 0;
    let mut v_name_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: u8 = 0;
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: u8 = 0;
    let mut v___x_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: u8 = 0;
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_4810_ = leanh::lean_ctor_get_uint8(
                    v_attr_4809_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_name_4811_ = leanh::lean_ctor_get(v_attr_4809_, 0);
                leanh::lean_inc(v_name_4811_);
                v_stx_4812_ = leanh::lean_ctor_get(v_attr_4809_, 1);
                leanh::lean_inc(v_stx_4812_);
                leanh::lean_dec_ref(v_attr_4809_);
                match v_kind_4810_ {
                    0 => {
                        v___x_4836_ = l_Lean_Elab_elabVisibility___redArg___lam__3___closed__4;
                        v___y_4814_ = v___x_4836_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_4837_ = l_Lean_Elab_instToFormatModifiers___lam__0___closed__6;
                        v___y_4814_ = v___x_4837_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_4838_ = l_Lean_Elab_instToFormatModifiers___lam__0___closed__7;
                        v___y_4814_ = v___x_4838_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_4814_);
                v___x_4815_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4815_, 0, v___y_4814_);
                v___x_4816_ = 1;
                v___x_4817_ = l_Lean_Name_toString(v_name_4811_, v___x_4816_);
                v___x_4818_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4818_, 0, v___x_4817_);
                v___x_4819_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4819_, 0, v___x_4815_);
                leanh::lean_ctor_set(v___x_4819_, 1, v___x_4818_);
                v___x_4820_ = leanh::lean_box(0);
                v___x_4821_ = 0;
                v___x_4822_ = l_Lean_Syntax_formatStx(v_stx_4812_, v___x_4820_, v___x_4821_);
                v___x_4823_ = l_Std_Format_defWidth;
                v___x_4824_ = leanh::lean_unsigned_to_nat(0);
                v___x_4825_ =
                    l_Std_Format_pretty(v___x_4822_, v___x_4823_, v___x_4824_, v___x_4824_);
                v___x_4826_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4826_, 0, v___x_4825_);
                v___x_4827_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4827_, 0, v___x_4819_);
                leanh::lean_ctor_set(v___x_4827_, 1, v___x_4826_);
                v___x_4828_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_instToFormatModifiers___lam__0___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_instToFormatModifiers___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Elab_instToFormatModifiers___lam__0___closed__3,
                );
                v___x_4829_ = l_Lean_Elab_instToFormatModifiers___lam__0___closed__4;
                v___x_4830_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4830_, 0, v___x_4829_);
                leanh::lean_ctor_set(v___x_4830_, 1, v___x_4827_);
                v___x_4831_ = l_Lean_Elab_instToFormatModifiers___lam__0___closed__5;
                v___x_4832_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4832_, 0, v___x_4830_);
                leanh::lean_ctor_set(v___x_4832_, 1, v___x_4831_);
                v___x_4833_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4833_, 0, v___x_4828_);
                leanh::lean_ctor_set(v___x_4833_, 1, v___x_4832_);
                v___x_4834_ = 0;
                v___x_4835_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4835_, 0, v___x_4833_);
                leanh::lean_ctor_set_uint8(
                    v___x_4835_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4834_,
                );
                return v___x_4835_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4847_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__0;
    v___x_4848_ = lean_string_length(v___x_4847_);
    return v___x_4848_;
}
pub unsafe fn _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4849_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__5_once),
        _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__5,
    );
    v___x_4850_ = lean_nat_to_int(v___x_4849_);
    return v___x_4850_;
}
pub unsafe fn _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4906_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__33;
    v___x_4907_ = lean_string_length(v___x_4906_);
    return v___x_4907_;
}
pub unsafe fn _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4908_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__35_once),
        _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__35,
    );
    v___x_4909_ = lean_nat_to_int(v___x_4908_);
    return v___x_4909_;
}
pub unsafe fn l_Lean_Elab_instToFormatModifiers___lam__1(
    mut v___f_4919_: *mut leanh::LeanObject,
    mut v___f_4920_: *mut leanh::LeanObject,
    mut v_m_4921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_docString_x3f_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visibility_4923_: u8 = 0;
    let mut v_isProtected_4924_: u8 = 0;
    let mut v_computeKind_4925_: u8 = 0;
    let mut v_recKind_4926_: u8 = 0;
    let mut v_isUnsafe_4927_: u8 = 0;
    let mut v_attrs_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_components_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: u8 = 0;
    let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4982_: u8 = 0;
    let mut v_fst_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4987_: u8 = 0;
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: u8 = 0;
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: u8 = 0;
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5020_: u8 = 0;
    let mut v_isSharedCheck_5021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_docString_x3f_4922_ = leanh::lean_ctor_get(v_m_4921_, 1);
                leanh::lean_inc(v_docString_x3f_4922_);
                v_visibility_4923_ = leanh::lean_ctor_get_uint8(
                    v_m_4921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_isProtected_4924_ = leanh::lean_ctor_get_uint8(
                    v_m_4921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_computeKind_4925_ = leanh::lean_ctor_get_uint8(
                    v_m_4921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                );
                v_recKind_4926_ = leanh::lean_ctor_get_uint8(
                    v_m_4921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3) as u32,
                );
                v_isUnsafe_4927_ = leanh::lean_ctor_get_uint8(
                    v_m_4921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4) as u32,
                );
                v_attrs_4928_ = leanh::lean_ctor_get(v_m_4921_, 2);
                leanh::lean_inc_ref(v_attrs_4928_);
                leanh::lean_dec_ref(v_m_4921_);
                if leanh::lean_obj_tag(v_docString_x3f_4922_) == 0 {
                    v___x_4978_ = leanh::lean_box(0);
                    v___y_4974_ = v___x_4978_;
                    state = 6;
                    continue;
                } else {
                    v_val_4979_ = leanh::lean_ctor_get(v_docString_x3f_4922_, 0);
                    v_isSharedCheck_5021_ =
                        (!leanh::lean_is_exclusive(v_docString_x3f_4922_)) as u8;
                    if v_isSharedCheck_5021_ == 0 {
                        v___x_4981_ = v_docString_x3f_4922_;
                        v_isShared_4982_ = v_isSharedCheck_5021_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4979_);
                        leanh::lean_dec(v_docString_x3f_4922_);
                        v___x_4981_ = leanh::lean_box(0);
                        v_isShared_4982_ = v_isSharedCheck_5021_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_4931_);
                v___x_4932_ = l_List_appendTR___redArg(v___y_4930_, v___y_4931_);
                v___x_4933_ = lean_array_to_list(v_attrs_4928_);
                v___x_4934_ = leanh::lean_box(0);
                v___x_4935_ = l_List_mapTR_loop___redArg(v___f_4919_, v___x_4933_, v___x_4934_);
                v_components_4936_ = l_List_appendTR___redArg(v___x_4932_, v___x_4935_);
                v___x_4937_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__3;
                v___x_4938_ =
                    l_Std_Format_joinSep___redArg(v___f_4920_, v_components_4936_, v___x_4937_);
                v___x_4939_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_instToFormatModifiers___lam__1___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_instToFormatModifiers___lam__1___closed__6_once
                    ),
                    _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__6,
                );
                v___x_4940_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__7;
                v___x_4941_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4941_, 0, v___x_4940_);
                leanh::lean_ctor_set(v___x_4941_, 1, v___x_4938_);
                v___x_4942_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__8;
                v___x_4943_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4943_, 0, v___x_4941_);
                leanh::lean_ctor_set(v___x_4943_, 1, v___x_4942_);
                v___x_4944_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4944_, 0, v___x_4939_);
                leanh::lean_ctor_set(v___x_4944_, 1, v___x_4943_);
                v___x_4945_ = 0;
                v___x_4946_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4946_, 0, v___x_4944_);
                leanh::lean_ctor_set_uint8(
                    v___x_4946_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4945_,
                );
                return v___x_4946_;
            }
            2 => {
                leanh::lean_inc(v___y_4949_);
                v___x_4950_ = l_List_appendTR___redArg(v___y_4948_, v___y_4949_);
                if v_isUnsafe_4927_ == 0 {
                    v___x_4951_ = leanh::lean_box(0);
                    v___y_4930_ = v___x_4950_;
                    v___y_4931_ = v___x_4951_;
                    state = 1;
                    continue;
                } else {
                    v___x_4952_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__11;
                    v___y_4930_ = v___x_4950_;
                    v___y_4931_ = v___x_4952_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v___y_4955_);
                v___x_4956_ = l_List_appendTR___redArg(v___y_4954_, v___y_4955_);
                match v_recKind_4926_ {
                    0 => {
                        v___x_4957_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__14;
                        v___y_4948_ = v___x_4956_;
                        v___y_4949_ = v___x_4957_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v___x_4958_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__17;
                        v___y_4948_ = v___x_4956_;
                        v___y_4949_ = v___x_4958_;
                        state = 2;
                        continue;
                    }
                    _ => {
                        v___x_4959_ = leanh::lean_box(0);
                        v___y_4948_ = v___x_4956_;
                        v___y_4949_ = v___x_4959_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                leanh::lean_inc(v___y_4962_);
                v___x_4963_ = l_List_appendTR___redArg(v___y_4961_, v___y_4962_);
                match v_computeKind_4925_ {
                    0 => {
                        v___x_4964_ = leanh::lean_box(0);
                        v___y_4954_ = v___x_4963_;
                        v___y_4955_ = v___x_4964_;
                        state = 3;
                        continue;
                    }
                    1 => {
                        v___x_4965_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__20;
                        v___y_4954_ = v___x_4963_;
                        v___y_4955_ = v___x_4965_;
                        state = 3;
                        continue;
                    }
                    _ => {
                        v___x_4966_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__23;
                        v___y_4954_ = v___x_4963_;
                        v___y_4955_ = v___x_4966_;
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_inc(v___y_4969_);
                v___x_4970_ = l_List_appendTR___redArg(v___y_4968_, v___y_4969_);
                if v_isProtected_4924_ == 0 {
                    v___x_4971_ = leanh::lean_box(0);
                    v___y_4961_ = v___x_4970_;
                    v___y_4962_ = v___x_4971_;
                    state = 4;
                    continue;
                } else {
                    v___x_4972_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__26;
                    v___y_4961_ = v___x_4970_;
                    v___y_4962_ = v___x_4972_;
                    state = 4;
                    continue;
                }
            }
            6 => match v_visibility_4923_ {
                0 => {
                    v___x_4975_ = leanh::lean_box(0);
                    v___y_4968_ = v___y_4974_;
                    v___y_4969_ = v___x_4975_;
                    state = 5;
                    continue;
                }
                1 => {
                    v___x_4976_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__28;
                    v___y_4968_ = v___y_4974_;
                    v___y_4969_ = v___x_4976_;
                    state = 5;
                    continue;
                }
                _ => {
                    v___x_4977_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__30;
                    v___y_4968_ = v___y_4974_;
                    v___y_4969_ = v___x_4977_;
                    state = 5;
                    continue;
                }
            },
            7 => {
                v_fst_4983_ = leanh::lean_ctor_get(v_val_4979_, 0);
                v_snd_4984_ = leanh::lean_ctor_get(v_val_4979_, 1);
                v_isSharedCheck_5020_ = (!leanh::lean_is_exclusive(v_val_4979_)) as u8;
                if v_isSharedCheck_5020_ == 0 {
                    v___x_4986_ = v_val_4979_;
                    v_isShared_4987_ = v_isSharedCheck_5020_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4984_);
                    leanh::lean_inc(v_fst_4983_);
                    leanh::lean_dec(v_val_4979_);
                    v___x_4986_ = leanh::lean_box(0);
                    v_isShared_4987_ = v_isSharedCheck_5020_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4988_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__32;
                v___x_4989_ = leanh::lean_box(0);
                v___x_4990_ = 0;
                v___x_4991_ = l_Lean_Syntax_formatStx(v_fst_4983_, v___x_4989_, v___x_4990_);
                v___x_4992_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__2;
                if v_isShared_4987_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4986_, 5);
                    leanh::lean_ctor_set(v___x_4986_, 1, v___x_4992_);
                    leanh::lean_ctor_set(v___x_4986_, 0, v___x_4991_);
                    v___x_4994_ = v___x_4986_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5019_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5019_, 0, v___x_4991_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5019_, 1, v___x_4992_);
                    v___x_4994_ = v_reuseFailAlloc_5019_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4995_ = leanh::lean_box(1);
                v___x_4996_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4996_, 0, v___x_4994_);
                leanh::lean_ctor_set(v___x_4996_, 1, v___x_4995_);
                v___x_5016_ = (leanh::lean_unbox(v_snd_4984_) as u8);
                leanh::lean_dec(v_snd_4984_);
                if v___x_5016_ == 0 {
                    v___x_5017_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__41;
                    v___y_4998_ = v___x_5017_;
                    state = 10;
                    continue;
                } else {
                    v___x_5018_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__42;
                    v___y_4998_ = v___x_5018_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                leanh::lean_inc_ref(v___y_4998_);
                if v_isShared_4982_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4981_, 3);
                    leanh::lean_ctor_set(v___x_4981_, 0, v___y_4998_);
                    v___x_5000_ = v___x_4981_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5015_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5015_, 0, v___y_4998_);
                    v___x_5000_ = v_reuseFailAlloc_5015_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_5001_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5001_, 0, v___x_4996_);
                leanh::lean_ctor_set(v___x_5001_, 1, v___x_5000_);
                v___x_5002_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_instToFormatModifiers___lam__1___closed__36
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_instToFormatModifiers___lam__1___closed__36_once
                    ),
                    _init_l_Lean_Elab_instToFormatModifiers___lam__1___closed__36,
                );
                v___x_5003_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__37;
                v___x_5004_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5004_, 0, v___x_5003_);
                leanh::lean_ctor_set(v___x_5004_, 1, v___x_5001_);
                v___x_5005_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__38;
                v___x_5006_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5006_, 0, v___x_5004_);
                leanh::lean_ctor_set(v___x_5006_, 1, v___x_5005_);
                v___x_5007_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5007_, 0, v___x_5002_);
                leanh::lean_ctor_set(v___x_5007_, 1, v___x_5006_);
                v___x_5008_ = 0;
                v___x_5009_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_5009_, 0, v___x_5007_);
                leanh::lean_ctor_set_uint8(
                    v___x_5009_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_5008_,
                );
                v___x_5010_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5010_, 0, v___x_4988_);
                leanh::lean_ctor_set(v___x_5010_, 1, v___x_5009_);
                v___x_5011_ = l_Lean_Elab_instToFormatModifiers___lam__1___closed__40;
                v___x_5012_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5012_, 0, v___x_5010_);
                leanh::lean_ctor_set(v___x_5012_, 1, v___x_5011_);
                v___x_5013_ = leanh::lean_box(0);
                v___x_5014_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5014_, 0, v___x_5012_);
                leanh::lean_ctor_set(v___x_5014_, 1, v___x_5013_);
                v___y_4974_ = v___x_5014_;
                state = 6;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_instToStringModifiers___lam__0(
    mut v_f_5028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5029_ = l_Std_Format_defWidth;
    v___x_5030_ = leanh::lean_unsigned_to_nat(0);
    v___x_5031_ = l_Std_Format_pretty(v_f_5028_, v___x_5029_, v___x_5030_, v___x_5030_);
    return v___x_5031_;
}
pub unsafe fn _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5038_ = l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__0;
    v___x_5039_ = l_Lean_stringToMessageData(v___x_5038_);
    return v___x_5039_;
}
pub unsafe fn l_Lean_Elab_expandOptDocComment_x3f___redArg(
    mut v_inst_5040_: *mut leanh::LeanObject,
    mut v_inst_5041_: *mut leanh::LeanObject,
    mut v_optDocComment_5042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5051_: u8 = 0;
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5069_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_5043_ = leanh::lean_ctor_get(v_inst_5040_, 0);
                v_toPure_5044_ = leanh::lean_ctor_get(v_toApplicative_5043_, 1);
                v___x_5045_ = l_Lean_Syntax_getOptional_x3f(v_optDocComment_5042_);
                if leanh::lean_obj_tag(v___x_5045_) == 0 {
                    leanh::lean_inc(v_toPure_5044_);
                    leanh::lean_dec_ref(v_inst_5041_);
                    leanh::lean_dec_ref(v_inst_5040_);
                    v___x_5046_ = leanh::lean_box(0);
                    v___x_5047_ = leanh::lean_apply_2(
                        v_toPure_5044_,
                        leanh::lean_box(0),
                        v___x_5046_,
                    );
                    return v___x_5047_;
                } else {
                    v_val_5048_ = leanh::lean_ctor_get(v___x_5045_, 0);
                    v_isSharedCheck_5069_ = (!leanh::lean_is_exclusive(v___x_5045_)) as u8;
                    if v_isSharedCheck_5069_ == 0 {
                        v___x_5050_ = v___x_5045_;
                        v_isShared_5051_ = v_isSharedCheck_5069_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5048_);
                        leanh::lean_dec(v___x_5045_);
                        v___x_5050_ = leanh::lean_box(0);
                        v_isShared_5051_ = v_isSharedCheck_5069_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5052_ = leanh::lean_unsigned_to_nat(1);
                v___x_5053_ = l_Lean_Syntax_getArg(v_val_5048_, v___x_5052_);
                if leanh::lean_obj_tag(v___x_5053_) == 2 {
                    leanh::lean_inc(v_toPure_5044_);
                    leanh::lean_dec(v_val_5048_);
                    leanh::lean_dec_ref(v_inst_5041_);
                    leanh::lean_dec_ref(v_inst_5040_);
                    v_val_5054_ = leanh::lean_ctor_get(v___x_5053_, 1);
                    leanh::lean_inc_ref(v_val_5054_);
                    leanh::lean_dec_ref_known(v___x_5053_, 2);
                    v___x_5055_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5056_ = lean_string_utf8_byte_size(v_val_5054_);
                    v___x_5057_ = leanh::lean_unsigned_to_nat(2);
                    v___x_5058_ = lean_nat_sub(v___x_5056_, v___x_5057_);
                    v___x_5059_ = lean_string_utf8_extract(v_val_5054_, v___x_5055_, v___x_5058_);
                    leanh::lean_dec(v___x_5058_);
                    leanh::lean_dec_ref(v_val_5054_);
                    if v_isShared_5051_ == 0 {
                        leanh::lean_ctor_set(v___x_5050_, 0, v___x_5059_);
                        v___x_5061_ = v___x_5050_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5063_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5059_);
                        v___x_5061_ = v_reuseFailAlloc_5063_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5050_);
                    v___x_5064_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1_once
                        ),
                        _init_l_Lean_Elab_expandOptDocComment_x3f___redArg___closed__1,
                    );
                    v___x_5065_ = l_Lean_MessageData_ofSyntax(v___x_5053_);
                    v___x_5066_ = l_Lean_indentD(v___x_5065_);
                    v___x_5067_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5067_, 0, v___x_5064_);
                    leanh::lean_ctor_set(v___x_5067_, 1, v___x_5066_);
                    v___x_5068_ = l_Lean_throwErrorAt___redArg(
                        v_inst_5040_,
                        v_inst_5041_,
                        v_val_5048_,
                        v___x_5067_,
                    );
                    return v___x_5068_;
                }
            }
            2 => {
                v___x_5062_ = leanh::lean_apply_2(
                    v_toPure_5044_,
                    leanh::lean_box(0),
                    v___x_5061_,
                );
                return v___x_5062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_expandOptDocComment_x3f___redArg___boxed(
    mut v_inst_5070_: *mut leanh::LeanObject,
    mut v_inst_5071_: *mut leanh::LeanObject,
    mut v_optDocComment_5072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5073_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(
        v_inst_5070_,
        v_inst_5071_,
        v_optDocComment_5072_,
    );
    leanh::lean_dec(v_optDocComment_5072_);
    return v_res_5073_;
}
pub unsafe fn l_Lean_Elab_expandOptDocComment_x3f(
    mut v_m_5074_: *mut leanh::LeanObject,
    mut v_inst_5075_: *mut leanh::LeanObject,
    mut v_inst_5076_: *mut leanh::LeanObject,
    mut v_optDocComment_5077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5078_ = l_Lean_Elab_expandOptDocComment_x3f___redArg(
        v_inst_5075_,
        v_inst_5076_,
        v_optDocComment_5077_,
    );
    return v___x_5078_;
}
pub unsafe fn l_Lean_Elab_expandOptDocComment_x3f___boxed(
    mut v_m_5079_: *mut leanh::LeanObject,
    mut v_inst_5080_: *mut leanh::LeanObject,
    mut v_inst_5081_: *mut leanh::LeanObject,
    mut v_optDocComment_5082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5083_ = l_Lean_Elab_expandOptDocComment_x3f(
        v_m_5079_,
        v_inst_5080_,
        v_inst_5081_,
        v_optDocComment_5082_,
    );
    leanh::lean_dec(v_optDocComment_5082_);
    return v_res_5083_;
}
pub unsafe fn l_Lean_Elab_elabModifiers___redArg___lam__0(
    mut v_stx_5084_: *mut leanh::LeanObject,
    mut v___y_5085_: *mut leanh::LeanObject,
    mut v_visibility_5086_: u8,
    mut v___y_5087_: u8,
    mut v___y_5088_: u8,
    mut v___y_5089_: u8,
    mut v_toPure_5090_: *mut leanh::LeanObject,
    mut v_unsafeStx_5091_: *mut leanh::LeanObject,
    mut v_attrs_5092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5094_: u8 = 0;
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: u8 = 0;
    let mut v___x_5098_: u8 = 0;
    let mut v___x_5099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5097_ = l_Lean_Syntax_isNone(v_unsafeStx_5091_);
                if v___x_5097_ == 0 {
                    v___x_5098_ = 1;
                    v___y_5094_ = v___x_5098_;
                    state = 1;
                    continue;
                } else {
                    v___x_5099_ = 0;
                    v___y_5094_ = v___x_5099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5095_ = leanh::lean_alloc_ctor(0, 3, (5) as u32);
                leanh::lean_ctor_set(v___x_5095_, 0, v_stx_5084_);
                leanh::lean_ctor_set(v___x_5095_, 1, v___y_5085_);
                leanh::lean_ctor_set(v___x_5095_, 2, v_attrs_5092_);
                leanh::lean_ctor_set_uint8(
                    v___x_5095_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v_visibility_5086_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5095_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                    v___y_5087_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5095_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                    v___y_5088_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5095_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3) as u32,
                    v___y_5089_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5095_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4) as u32,
                    v___y_5094_,
                );
                v___x_5096_ = leanh::lean_apply_2(
                    v_toPure_5090_,
                    leanh::lean_box(0),
                    v___x_5095_,
                );
                return v___x_5096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabModifiers___redArg___lam__0___boxed(
    mut v_stx_5100_: *mut leanh::LeanObject,
    mut v___y_5101_: *mut leanh::LeanObject,
    mut v_visibility_5102_: *mut leanh::LeanObject,
    mut v___y_5103_: *mut leanh::LeanObject,
    mut v___y_5104_: *mut leanh::LeanObject,
    mut v___y_5105_: *mut leanh::LeanObject,
    mut v_toPure_5106_: *mut leanh::LeanObject,
    mut v_unsafeStx_5107_: *mut leanh::LeanObject,
    mut v_attrs_5108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_visibility_boxed_5109_: u8 = 0;
    let mut v___y_482__boxed_5110_: u8 = 0;
    let mut v___y_483__boxed_5111_: u8 = 0;
    let mut v___y_484__boxed_5112_: u8 = 0;
    let mut v_res_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_visibility_boxed_5109_ = (leanh::lean_unbox(v_visibility_5102_) as u8);
    v___y_482__boxed_5110_ = (leanh::lean_unbox(v___y_5103_) as u8);
    v___y_483__boxed_5111_ = (leanh::lean_unbox(v___y_5104_) as u8);
    v___y_484__boxed_5112_ = (leanh::lean_unbox(v___y_5105_) as u8);
    v_res_5113_ = l_Lean_Elab_elabModifiers___redArg___lam__0(
        v_stx_5100_,
        v___y_5101_,
        v_visibility_boxed_5109_,
        v___y_482__boxed_5110_,
        v___y_483__boxed_5111_,
        v___y_484__boxed_5112_,
        v_toPure_5106_,
        v_unsafeStx_5107_,
        v_attrs_5108_,
    );
    leanh::lean_dec(v_unsafeStx_5107_);
    return v_res_5113_;
}
pub unsafe fn l_Lean_Elab_elabModifiers___redArg___lam__1(
    mut v___f_5114_: *mut leanh::LeanObject,
    mut v_attrs_5115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5116_ = leanh::lean_apply_1(v___f_5114_, v_attrs_5115_);
    return v___x_5116_;
}
pub unsafe fn l_Lean_Elab_elabModifiers___redArg___lam__3(
    mut v_stx_5117_: *mut leanh::LeanObject,
    mut v___y_5118_: *mut leanh::LeanObject,
    mut v___y_5119_: u8,
    mut v___y_5120_: u8,
    mut v_toPure_5121_: *mut leanh::LeanObject,
    mut v_unsafeStx_5122_: *mut leanh::LeanObject,
    mut v_attrsStx_5123_: *mut leanh::LeanObject,
    mut v___x_5124_: *mut leanh::LeanObject,
    mut v_toBind_5125_: *mut leanh::LeanObject,
    mut v_inst_5126_: *mut leanh::LeanObject,
    mut v_inst_5127_: *mut leanh::LeanObject,
    mut v_inst_5128_: *mut leanh::LeanObject,
    mut v_inst_5129_: *mut leanh::LeanObject,
    mut v_inst_5130_: *mut leanh::LeanObject,
    mut v_inst_5131_: *mut leanh::LeanObject,
    mut v_inst_5132_: *mut leanh::LeanObject,
    mut v_inst_5133_: *mut leanh::LeanObject,
    mut v_inst_5134_: *mut leanh::LeanObject,
    mut v_inst_5135_: *mut leanh::LeanObject,
    mut v_inst_5136_: *mut leanh::LeanObject,
    mut v_inst_5137_: *mut leanh::LeanObject,
    mut v_protectedStx_5138_: *mut leanh::LeanObject,
    mut v_visibility_5139_: u8,
) -> *mut leanh::LeanObject {
    let mut v___y_5141_: u8 = 0;
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: u8 = 0;
    let mut v___x_5157_: u8 = 0;
    let mut v___x_5158_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5156_ = l_Lean_Syntax_isNone(v_protectedStx_5138_);
                if v___x_5156_ == 0 {
                    v___x_5157_ = 1;
                    v___y_5141_ = v___x_5157_;
                    state = 1;
                    continue;
                } else {
                    v___x_5158_ = 0;
                    v___y_5141_ = v___x_5158_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5142_ = leanh::lean_box((v_visibility_5139_) as usize);
                v___x_5143_ = leanh::lean_box((v___y_5141_) as usize);
                v___x_5144_ = leanh::lean_box((v___y_5119_) as usize);
                v___x_5145_ = leanh::lean_box((v___y_5120_) as usize);
                leanh::lean_inc(v_toPure_5121_);
                v___f_5146_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_elabModifiers___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    8,
                );
                leanh::lean_closure_set(v___f_5146_, 0, v_stx_5117_);
                leanh::lean_closure_set(v___f_5146_, 1, v___y_5118_);
                leanh::lean_closure_set(v___f_5146_, 2, v___x_5142_);
                leanh::lean_closure_set(v___f_5146_, 3, v___x_5143_);
                leanh::lean_closure_set(v___f_5146_, 4, v___x_5144_);
                leanh::lean_closure_set(v___f_5146_, 5, v___x_5145_);
                leanh::lean_closure_set(v___f_5146_, 6, v_toPure_5121_);
                leanh::lean_closure_set(v___f_5146_, 7, v_unsafeStx_5122_);
                v___x_5147_ = l_Lean_Syntax_getOptional_x3f(v_attrsStx_5123_);
                if leanh::lean_obj_tag(v___x_5147_) == 0 {
                    leanh::lean_dec(v_inst_5137_);
                    leanh::lean_dec(v_inst_5136_);
                    leanh::lean_dec_ref(v_inst_5135_);
                    leanh::lean_dec(v_inst_5134_);
                    leanh::lean_dec(v_inst_5133_);
                    leanh::lean_dec_ref(v_inst_5132_);
                    leanh::lean_dec_ref(v_inst_5131_);
                    leanh::lean_dec_ref(v_inst_5130_);
                    leanh::lean_dec_ref(v_inst_5129_);
                    leanh::lean_dec_ref(v_inst_5128_);
                    leanh::lean_dec_ref(v_inst_5127_);
                    leanh::lean_dec_ref(v_inst_5126_);
                    v___f_5148_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_elabModifiers___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_5148_, 0, v___f_5146_);
                    v___x_5149_ = lean_mk_empty_array_with_capacity(v___x_5124_);
                    v___x_5150_ = leanh::lean_apply_2(
                        v_toPure_5121_,
                        leanh::lean_box(0),
                        v___x_5149_,
                    );
                    v___x_5151_ = leanh::lean_apply_4(
                        v_toBind_5125_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_5150_,
                        v___f_5148_,
                    );
                    return v___x_5151_;
                } else {
                    leanh::lean_dec(v_toPure_5121_);
                    v_val_5152_ = leanh::lean_ctor_get(v___x_5147_, 0);
                    leanh::lean_inc(v_val_5152_);
                    leanh::lean_dec_ref_known(v___x_5147_, 1);
                    v___f_5153_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_elabModifiers___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_5153_, 0, v___f_5146_);
                    v___x_5154_ = l_Lean_Elab_elabDeclAttrs___redArg(
                        v_inst_5126_,
                        v_inst_5127_,
                        v_inst_5128_,
                        v_inst_5129_,
                        v_inst_5130_,
                        v_inst_5131_,
                        v_inst_5132_,
                        v_inst_5133_,
                        v_inst_5134_,
                        v_inst_5135_,
                        v_inst_5136_,
                        v_inst_5137_,
                        v_val_5152_,
                    );
                    leanh::lean_dec(v_val_5152_);
                    v___x_5155_ = leanh::lean_apply_4(
                        v_toBind_5125_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_5154_,
                        v___f_5153_,
                    );
                    return v___x_5155_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabModifiers___redArg___lam__3___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stx_5159_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___y_5160_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___y_5161_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___y_5162_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_toPure_5163_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_unsafeStx_5164_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_attrsStx_5165_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_5166_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_toBind_5167_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_inst_5168_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_inst_5169_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_inst_5170_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_inst_5171_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_inst_5172_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_inst_5173_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_inst_5174_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_inst_5175_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_inst_5176_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_inst_5177_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_inst_5178_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_inst_5179_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_protectedStx_5180_: *mut leanh::LeanObject = *_args.add(21);
    let mut v_visibility_5181_: *mut leanh::LeanObject = *_args.add(22);
    let mut v___y_512__boxed_5182_: u8 = 0;
    let mut v___y_513__boxed_5183_: u8 = 0;
    let mut v_visibility_boxed_5184_: u8 = 0;
    let mut v_res_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_512__boxed_5182_ = (leanh::lean_unbox(v___y_5161_) as u8);
    v___y_513__boxed_5183_ = (leanh::lean_unbox(v___y_5162_) as u8);
    v_visibility_boxed_5184_ = (leanh::lean_unbox(v_visibility_5181_) as u8);
    v_res_5185_ = l_Lean_Elab_elabModifiers___redArg___lam__3(
        v_stx_5159_,
        v___y_5160_,
        v___y_512__boxed_5182_,
        v___y_513__boxed_5183_,
        v_toPure_5163_,
        v_unsafeStx_5164_,
        v_attrsStx_5165_,
        v___x_5166_,
        v_toBind_5167_,
        v_inst_5168_,
        v_inst_5169_,
        v_inst_5170_,
        v_inst_5171_,
        v_inst_5172_,
        v_inst_5173_,
        v_inst_5174_,
        v_inst_5175_,
        v_inst_5176_,
        v_inst_5177_,
        v_inst_5178_,
        v_inst_5179_,
        v_protectedStx_5180_,
        v_visibility_boxed_5184_,
    );
    leanh::lean_dec(v_protectedStx_5180_);
    leanh::lean_dec(v___x_5166_);
    leanh::lean_dec(v_attrsStx_5165_);
    return v_res_5185_;
}
pub unsafe fn l_Lean_Elab_elabModifiers___redArg___lam__2(
    mut v_inst_5186_: *mut leanh::LeanObject,
    mut v_inst_5187_: *mut leanh::LeanObject,
    mut v_inst_5188_: *mut leanh::LeanObject,
    mut v_inst_5189_: *mut leanh::LeanObject,
    mut v_inst_5190_: *mut leanh::LeanObject,
    mut v_inst_5191_: *mut leanh::LeanObject,
    mut v_toBind_5192_: *mut leanh::LeanObject,
    mut v_stx_5193_: *mut leanh::LeanObject,
    mut v___y_5194_: u8,
    mut v___y_5195_: u8,
    mut v_toPure_5196_: *mut leanh::LeanObject,
    mut v_unsafeStx_5197_: *mut leanh::LeanObject,
    mut v_attrsStx_5198_: *mut leanh::LeanObject,
    mut v___x_5199_: *mut leanh::LeanObject,
    mut v_inst_5200_: *mut leanh::LeanObject,
    mut v_inst_5201_: *mut leanh::LeanObject,
    mut v_inst_5202_: *mut leanh::LeanObject,
    mut v_inst_5203_: *mut leanh::LeanObject,
    mut v_inst_5204_: *mut leanh::LeanObject,
    mut v_inst_5205_: *mut leanh::LeanObject,
    mut v_protectedStx_5206_: *mut leanh::LeanObject,
    mut v_visibilityStx_5207_: *mut leanh::LeanObject,
    mut v_docCommentStx_5208_: *mut leanh::LeanObject,
    mut v___x_5209_: *mut leanh::LeanObject,
    mut v_____do__lift_5210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5226_: u8 = 0;
    let mut v___x_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5230_: u8 = 0;
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5236_: u8 = 0;
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5231_ = l_Lean_Syntax_getOptional_x3f(v_docCommentStx_5208_);
                if leanh::lean_obj_tag(v___x_5231_) == 0 {
                    leanh::lean_dec_ref(v___x_5209_);
                    v___x_5232_ = leanh::lean_box(0);
                    v___y_5217_ = v___x_5232_;
                    state = 2;
                    continue;
                } else {
                    v_val_5233_ = leanh::lean_ctor_get(v___x_5231_, 0);
                    v_isSharedCheck_5243_ = (!leanh::lean_is_exclusive(v___x_5231_)) as u8;
                    if v_isSharedCheck_5243_ == 0 {
                        v___x_5235_ = v___x_5231_;
                        v_isShared_5236_ = v_isSharedCheck_5243_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5233_);
                        leanh::lean_dec(v___x_5231_);
                        v___x_5235_ = leanh::lean_box(0);
                        v_isShared_5236_ = v_isSharedCheck_5243_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5214_ = l_Lean_Elab_elabVisibility___redArg(
                    v_inst_5186_,
                    v_inst_5187_,
                    v_inst_5188_,
                    v_inst_5189_,
                    v_inst_5190_,
                    v_inst_5191_,
                    v___y_5213_,
                );
                v___x_5215_ = leanh::lean_apply_4(
                    v_toBind_5192_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_5214_,
                    v___y_5212_,
                );
                return v___x_5215_;
            }
            2 => {
                v___x_5218_ = leanh::lean_box((v___y_5194_) as usize);
                v___x_5219_ = leanh::lean_box((v___y_5195_) as usize);
                leanh::lean_inc_ref(v_inst_5190_);
                leanh::lean_inc(v_inst_5191_);
                leanh::lean_inc(v_inst_5189_);
                leanh::lean_inc_ref(v_inst_5187_);
                leanh::lean_inc_ref(v_inst_5188_);
                leanh::lean_inc_ref(v_inst_5186_);
                leanh::lean_inc(v_toBind_5192_);
                v___f_5220_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_elabModifiers___redArg___lam__3___boxed as *mut core::ffi::c_void,
                    23,
                    22,
                );
                leanh::lean_closure_set(v___f_5220_, 0, v_stx_5193_);
                leanh::lean_closure_set(v___f_5220_, 1, v___y_5217_);
                leanh::lean_closure_set(v___f_5220_, 2, v___x_5218_);
                leanh::lean_closure_set(v___f_5220_, 3, v___x_5219_);
                leanh::lean_closure_set(v___f_5220_, 4, v_toPure_5196_);
                leanh::lean_closure_set(v___f_5220_, 5, v_unsafeStx_5197_);
                leanh::lean_closure_set(v___f_5220_, 6, v_attrsStx_5198_);
                leanh::lean_closure_set(v___f_5220_, 7, v___x_5199_);
                leanh::lean_closure_set(v___f_5220_, 8, v_toBind_5192_);
                leanh::lean_closure_set(v___f_5220_, 9, v_inst_5186_);
                leanh::lean_closure_set(v___f_5220_, 10, v_inst_5188_);
                leanh::lean_closure_set(v___f_5220_, 11, v_inst_5200_);
                leanh::lean_closure_set(v___f_5220_, 12, v_inst_5187_);
                leanh::lean_closure_set(v___f_5220_, 13, v_inst_5201_);
                leanh::lean_closure_set(v___f_5220_, 14, v_inst_5202_);
                leanh::lean_closure_set(v___f_5220_, 15, v_inst_5203_);
                leanh::lean_closure_set(v___f_5220_, 16, v_inst_5189_);
                leanh::lean_closure_set(v___f_5220_, 17, v_inst_5191_);
                leanh::lean_closure_set(v___f_5220_, 18, v_inst_5190_);
                leanh::lean_closure_set(v___f_5220_, 19, v_inst_5204_);
                leanh::lean_closure_set(v___f_5220_, 20, v_inst_5205_);
                leanh::lean_closure_set(v___f_5220_, 21, v_protectedStx_5206_);
                v___x_5221_ = l_Lean_Syntax_getOptional_x3f(v_visibilityStx_5207_);
                if leanh::lean_obj_tag(v___x_5221_) == 0 {
                    v___x_5222_ = leanh::lean_box(0);
                    v___y_5212_ = v___f_5220_;
                    v___y_5213_ = v___x_5222_;
                    state = 1;
                    continue;
                } else {
                    v_val_5223_ = leanh::lean_ctor_get(v___x_5221_, 0);
                    v_isSharedCheck_5230_ = (!leanh::lean_is_exclusive(v___x_5221_)) as u8;
                    if v_isSharedCheck_5230_ == 0 {
                        v___x_5225_ = v___x_5221_;
                        v_isShared_5226_ = v_isSharedCheck_5230_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5223_);
                        leanh::lean_dec(v___x_5221_);
                        v___x_5225_ = leanh::lean_box(0);
                        v_isShared_5226_ = v_isSharedCheck_5230_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5226_ == 0 {
                    v___x_5228_ = v___x_5225_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5229_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_val_5223_);
                    v___x_5228_ = v_reuseFailAlloc_5229_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_5212_ = v___f_5220_;
                v___y_5213_ = v___x_5228_;
                state = 1;
                continue;
            }
            5 => {
                v___x_5237_ = l_Lean_doc_verso;
                v___x_5238_ =
                    l_Lean_Option_get___redArg(v___x_5209_, v_____do__lift_5210_, v___x_5237_);
                v___x_5239_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5239_, 0, v_val_5233_);
                leanh::lean_ctor_set(v___x_5239_, 1, v___x_5238_);
                if v_isShared_5236_ == 0 {
                    leanh::lean_ctor_set(v___x_5235_, 0, v___x_5239_);
                    v___x_5241_ = v___x_5235_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5242_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5242_, 0, v___x_5239_);
                    v___x_5241_ = v_reuseFailAlloc_5242_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_5217_ = v___x_5241_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabModifiers___redArg___lam__2___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_5244_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_inst_5245_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_inst_5246_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_5247_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_inst_5248_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_5249_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_toBind_5250_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_stx_5251_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5252_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_5253_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_toPure_5254_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_unsafeStx_5255_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_attrsStx_5256_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___x_5257_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_inst_5258_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_inst_5259_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_inst_5260_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_inst_5261_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_inst_5262_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_inst_5263_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_protectedStx_5264_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_visibilityStx_5265_: *mut leanh::LeanObject = *_args.add(21);
    let mut v_docCommentStx_5266_: *mut leanh::LeanObject = *_args.add(22);
    let mut v___x_5267_: *mut leanh::LeanObject = *_args.add(23);
    let mut v_____do__lift_5268_: *mut leanh::LeanObject = *_args.add(24);
    let mut v___y_603__boxed_5269_: u8 = 0;
    let mut v___y_604__boxed_5270_: u8 = 0;
    let mut v_res_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_603__boxed_5269_ = (leanh::lean_unbox(v___y_5252_) as u8);
    v___y_604__boxed_5270_ = (leanh::lean_unbox(v___y_5253_) as u8);
    v_res_5271_ = l_Lean_Elab_elabModifiers___redArg___lam__2(
        v_inst_5244_,
        v_inst_5245_,
        v_inst_5246_,
        v_inst_5247_,
        v_inst_5248_,
        v_inst_5249_,
        v_toBind_5250_,
        v_stx_5251_,
        v___y_603__boxed_5269_,
        v___y_604__boxed_5270_,
        v_toPure_5254_,
        v_unsafeStx_5255_,
        v_attrsStx_5256_,
        v___x_5257_,
        v_inst_5258_,
        v_inst_5259_,
        v_inst_5260_,
        v_inst_5261_,
        v_inst_5262_,
        v_inst_5263_,
        v_protectedStx_5264_,
        v_visibilityStx_5265_,
        v_docCommentStx_5266_,
        v___x_5267_,
        v_____do__lift_5268_,
    );
    leanh::lean_dec_ref(v_____do__lift_5268_);
    leanh::lean_dec(v_docCommentStx_5266_);
    leanh::lean_dec(v_visibilityStx_5265_);
    return v_res_5271_;
}
pub unsafe fn l_Lean_Elab_elabModifiers___redArg(
    mut v_inst_5282_: *mut leanh::LeanObject,
    mut v_inst_5283_: *mut leanh::LeanObject,
    mut v_inst_5284_: *mut leanh::LeanObject,
    mut v_inst_5285_: *mut leanh::LeanObject,
    mut v_inst_5286_: *mut leanh::LeanObject,
    mut v_inst_5287_: *mut leanh::LeanObject,
    mut v_inst_5288_: *mut leanh::LeanObject,
    mut v_inst_5289_: *mut leanh::LeanObject,
    mut v_inst_5290_: *mut leanh::LeanObject,
    mut v_inst_5291_: *mut leanh::LeanObject,
    mut v_inst_5292_: *mut leanh::LeanObject,
    mut v_inst_5293_: *mut leanh::LeanObject,
    mut v_stx_5294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_docCommentStx_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrsStx_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visibilityStx_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_protectedStx_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5308_: u8 = 0;
    let mut v___y_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5310_: u8 = 0;
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5316_: u8 = 0;
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unsafeStx_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: u8 = 0;
    let mut v___x_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: u8 = 0;
    let mut v___x_5326_: u8 = 0;
    let mut v___x_5327_: u8 = 0;
    let mut v___x_5328_: u8 = 0;
    let mut v___x_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: u8 = 0;
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: u8 = 0;
    let mut v___x_5336_: u8 = 0;
    let mut v___x_5337_: u8 = 0;
    let mut v___x_5338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5295_ = l_Lean_KVMap_instValueBool;
                v_toApplicative_5296_ = leanh::lean_ctor_get(v_inst_5282_, 0);
                v_toBind_5297_ = leanh::lean_ctor_get(v_inst_5282_, 1);
                leanh::lean_inc(v_toBind_5297_);
                v_toPure_5298_ = leanh::lean_ctor_get(v_toApplicative_5296_, 1);
                leanh::lean_inc(v_toPure_5298_);
                v___x_5299_ = leanh::lean_unsigned_to_nat(0);
                v_docCommentStx_5300_ = l_Lean_Syntax_getArg(v_stx_5294_, v___x_5299_);
                v___x_5301_ = leanh::lean_unsigned_to_nat(1);
                v_attrsStx_5302_ = l_Lean_Syntax_getArg(v_stx_5294_, v___x_5301_);
                v___x_5303_ = leanh::lean_unsigned_to_nat(2);
                v_visibilityStx_5304_ = l_Lean_Syntax_getArg(v_stx_5294_, v___x_5303_);
                v___x_5305_ = leanh::lean_unsigned_to_nat(3);
                v_protectedStx_5306_ = l_Lean_Syntax_getArg(v_stx_5294_, v___x_5305_);
                v___x_5329_ = leanh::lean_unsigned_to_nat(4);
                v___x_5330_ = l_Lean_Syntax_getArg(v_stx_5294_, v___x_5329_);
                v___x_5331_ = l_Lean_Syntax_isNone(v___x_5330_);
                if v___x_5331_ == 0 {
                    v___x_5332_ = l_Lean_Syntax_getArg(v___x_5330_, v___x_5299_);
                    leanh::lean_dec(v___x_5330_);
                    v___x_5333_ = l_Lean_Syntax_getKind(v___x_5332_);
                    v___x_5334_ = l_Lean_Elab_elabModifiers___redArg___closed__1;
                    v___x_5335_ = lean_name_eq(v___x_5333_, v___x_5334_);
                    leanh::lean_dec(v___x_5333_);
                    if v___x_5335_ == 0 {
                        v___x_5336_ = 2;
                        v___y_5316_ = v___x_5336_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5337_ = 1;
                        v___y_5316_ = v___x_5337_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_5330_);
                    v___x_5338_ = 0;
                    v___y_5316_ = v___x_5338_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5311_ = leanh::lean_box((v___y_5308_) as usize);
                v___x_5312_ = leanh::lean_box((v___y_5310_) as usize);
                leanh::lean_inc(v_toBind_5297_);
                leanh::lean_inc(v_inst_5290_);
                v___f_5313_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_elabModifiers___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    25,
                    24,
                );
                leanh::lean_closure_set(v___f_5313_, 0, v_inst_5282_);
                leanh::lean_closure_set(v___f_5313_, 1, v_inst_5285_);
                leanh::lean_closure_set(v___f_5313_, 2, v_inst_5283_);
                leanh::lean_closure_set(v___f_5313_, 3, v_inst_5290_);
                leanh::lean_closure_set(v___f_5313_, 4, v_inst_5292_);
                leanh::lean_closure_set(v___f_5313_, 5, v_inst_5291_);
                leanh::lean_closure_set(v___f_5313_, 6, v_toBind_5297_);
                leanh::lean_closure_set(v___f_5313_, 7, v_stx_5294_);
                leanh::lean_closure_set(v___f_5313_, 8, v___x_5311_);
                leanh::lean_closure_set(v___f_5313_, 9, v___x_5312_);
                leanh::lean_closure_set(v___f_5313_, 10, v_toPure_5298_);
                leanh::lean_closure_set(v___f_5313_, 11, v___y_5309_);
                leanh::lean_closure_set(v___f_5313_, 12, v_attrsStx_5302_);
                leanh::lean_closure_set(v___f_5313_, 13, v___x_5299_);
                leanh::lean_closure_set(v___f_5313_, 14, v_inst_5284_);
                leanh::lean_closure_set(v___f_5313_, 15, v_inst_5287_);
                leanh::lean_closure_set(v___f_5313_, 16, v_inst_5288_);
                leanh::lean_closure_set(v___f_5313_, 17, v_inst_5289_);
                leanh::lean_closure_set(v___f_5313_, 18, v_inst_5293_);
                leanh::lean_closure_set(v___f_5313_, 19, v_inst_5286_);
                leanh::lean_closure_set(v___f_5313_, 20, v_protectedStx_5306_);
                leanh::lean_closure_set(v___f_5313_, 21, v_visibilityStx_5304_);
                leanh::lean_closure_set(v___f_5313_, 22, v_docCommentStx_5300_);
                leanh::lean_closure_set(v___f_5313_, 23, v___x_5295_);
                v___x_5314_ = leanh::lean_apply_4(
                    v_toBind_5297_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_5290_,
                    v___f_5313_,
                );
                return v___x_5314_;
            }
            2 => {
                v___x_5317_ = leanh::lean_unsigned_to_nat(5);
                v_unsafeStx_5318_ = l_Lean_Syntax_getArg(v_stx_5294_, v___x_5317_);
                v___x_5319_ = leanh::lean_unsigned_to_nat(6);
                v___x_5320_ = l_Lean_Syntax_getArg(v_stx_5294_, v___x_5319_);
                v___x_5321_ = l_Lean_Syntax_isNone(v___x_5320_);
                if v___x_5321_ == 0 {
                    v___x_5322_ = l_Lean_Syntax_getArg(v___x_5320_, v___x_5299_);
                    leanh::lean_dec(v___x_5320_);
                    v___x_5323_ = l_Lean_Syntax_getKind(v___x_5322_);
                    v___x_5324_ = l_Lean_Elab_elabModifiers___redArg___closed__0;
                    v___x_5325_ = lean_name_eq(v___x_5323_, v___x_5324_);
                    leanh::lean_dec(v___x_5323_);
                    if v___x_5325_ == 0 {
                        v___x_5326_ = 1;
                        v___y_5308_ = v___y_5316_;
                        v___y_5309_ = v_unsafeStx_5318_;
                        v___y_5310_ = v___x_5326_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5327_ = 0;
                        v___y_5308_ = v___y_5316_;
                        v___y_5309_ = v_unsafeStx_5318_;
                        v___y_5310_ = v___x_5327_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_5320_);
                    v___x_5328_ = 2;
                    v___y_5308_ = v___y_5316_;
                    v___y_5309_ = v_unsafeStx_5318_;
                    v___y_5310_ = v___x_5328_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabModifiers(
    mut v_m_5339_: *mut leanh::LeanObject,
    mut v_inst_5340_: *mut leanh::LeanObject,
    mut v_inst_5341_: *mut leanh::LeanObject,
    mut v_inst_5342_: *mut leanh::LeanObject,
    mut v_inst_5343_: *mut leanh::LeanObject,
    mut v_inst_5344_: *mut leanh::LeanObject,
    mut v_inst_5345_: *mut leanh::LeanObject,
    mut v_inst_5346_: *mut leanh::LeanObject,
    mut v_inst_5347_: *mut leanh::LeanObject,
    mut v_inst_5348_: *mut leanh::LeanObject,
    mut v_inst_5349_: *mut leanh::LeanObject,
    mut v_inst_5350_: *mut leanh::LeanObject,
    mut v_inst_5351_: *mut leanh::LeanObject,
    mut v_stx_5352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5353_ = l_Lean_Elab_elabModifiers___redArg(
        v_inst_5340_,
        v_inst_5341_,
        v_inst_5342_,
        v_inst_5343_,
        v_inst_5344_,
        v_inst_5345_,
        v_inst_5346_,
        v_inst_5347_,
        v_inst_5348_,
        v_inst_5349_,
        v_inst_5350_,
        v_inst_5351_,
        v_stx_5352_,
    );
    return v___x_5353_;
}
pub unsafe fn l_Lean_Elab_applyVisibility___redArg___lam__0(
    mut v_toPure_5354_: *mut leanh::LeanObject,
    mut v_declName_5355_: *mut leanh::LeanObject,
    mut v_____r_5356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5357_ =
        leanh::lean_apply_2(v_toPure_5354_, leanh::lean_box(0), v_declName_5355_);
    return v___x_5357_;
}
pub unsafe fn l_Lean_Elab_applyVisibility___redArg___lam__1(
    mut v_declName_5358_: *mut leanh::LeanObject,
    mut v_env_5359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5360_ = l_Lean_addProtected(v_env_5359_, v_declName_5358_);
    return v___x_5360_;
}
pub unsafe fn l_Lean_Elab_applyVisibility___redArg___lam__2(
    mut v_modifiers_5361_: *mut leanh::LeanObject,
    mut v_toPure_5362_: *mut leanh::LeanObject,
    mut v_declName_5363_: *mut leanh::LeanObject,
    mut v_modifyEnv_5364_: *mut leanh::LeanObject,
    mut v___f_5365_: *mut leanh::LeanObject,
    mut v_toBind_5366_: *mut leanh::LeanObject,
    mut v___f_5367_: *mut leanh::LeanObject,
    mut v_____r_5368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isProtected_5369_: u8 = 0;
    v_isProtected_5369_ = leanh::lean_ctor_get_uint8(
        v_modifiers_5361_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
    );
    if v_isProtected_5369_ == 0 {
        let mut v___x_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_5367_);
        leanh::lean_dec(v_toBind_5366_);
        leanh::lean_dec_ref(v___f_5365_);
        leanh::lean_dec(v_modifyEnv_5364_);
        v___x_5370_ =
            leanh::lean_apply_2(v_toPure_5362_, leanh::lean_box(0), v_declName_5363_);
        return v___x_5370_;
    } else {
        let mut v___x_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_declName_5363_);
        leanh::lean_dec(v_toPure_5362_);
        v___x_5371_ = leanh::lean_apply_1(v_modifyEnv_5364_, v___f_5365_);
        v___x_5372_ = leanh::lean_apply_4(
            v_toBind_5366_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_5371_,
            v___f_5367_,
        );
        return v___x_5372_;
    }
}
pub unsafe fn l_Lean_Elab_applyVisibility___redArg___lam__2___boxed(
    mut v_modifiers_5373_: *mut leanh::LeanObject,
    mut v_toPure_5374_: *mut leanh::LeanObject,
    mut v_declName_5375_: *mut leanh::LeanObject,
    mut v_modifyEnv_5376_: *mut leanh::LeanObject,
    mut v___f_5377_: *mut leanh::LeanObject,
    mut v_toBind_5378_: *mut leanh::LeanObject,
    mut v___f_5379_: *mut leanh::LeanObject,
    mut v_____r_5380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5381_ = l_Lean_Elab_applyVisibility___redArg___lam__2(
        v_modifiers_5373_,
        v_toPure_5374_,
        v_declName_5375_,
        v_modifyEnv_5376_,
        v___f_5377_,
        v_toBind_5378_,
        v___f_5379_,
        v_____r_5380_,
    );
    leanh::lean_dec_ref(v_modifiers_5373_);
    return v_res_5381_;
}
pub unsafe fn l_Lean_Elab_applyVisibility___redArg___lam__3(
    mut v_toPure_5382_: *mut leanh::LeanObject,
    mut v_modifiers_5383_: *mut leanh::LeanObject,
    mut v_modifyEnv_5384_: *mut leanh::LeanObject,
    mut v_toBind_5385_: *mut leanh::LeanObject,
    mut v_inst_5386_: *mut leanh::LeanObject,
    mut v_inst_5387_: *mut leanh::LeanObject,
    mut v_inst_5388_: *mut leanh::LeanObject,
    mut v_inst_5389_: *mut leanh::LeanObject,
    mut v_inst_5390_: *mut leanh::LeanObject,
    mut v_____r_5391_: *mut leanh::LeanObject,
    mut v_declName_5392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_declName_5392_, 3);
    leanh::lean_inc(v_toPure_5382_);
    v___f_5393_ = leanh::lean_alloc_closure(
        l_Lean_Elab_applyVisibility___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5393_, 0, v_toPure_5382_);
    leanh::lean_closure_set(v___f_5393_, 1, v_declName_5392_);
    v___f_5394_ = leanh::lean_alloc_closure(
        l_Lean_Elab_applyVisibility___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5394_, 0, v_declName_5392_);
    leanh::lean_inc(v_toBind_5385_);
    v___f_5395_ = leanh::lean_alloc_closure(
        l_Lean_Elab_applyVisibility___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_5395_, 0, v_modifiers_5383_);
    leanh::lean_closure_set(v___f_5395_, 1, v_toPure_5382_);
    leanh::lean_closure_set(v___f_5395_, 2, v_declName_5392_);
    leanh::lean_closure_set(v___f_5395_, 3, v_modifyEnv_5384_);
    leanh::lean_closure_set(v___f_5395_, 4, v___f_5394_);
    leanh::lean_closure_set(v___f_5395_, 5, v_toBind_5385_);
    leanh::lean_closure_set(v___f_5395_, 6, v___f_5393_);
    v___x_5396_ = l_Lean_Elab_checkNotAlreadyDeclared___redArg(
        v_inst_5386_,
        v_inst_5387_,
        v_inst_5388_,
        v_inst_5389_,
        v_inst_5390_,
        v_declName_5392_,
    );
    v___x_5397_ = leanh::lean_apply_4(
        v_toBind_5385_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5396_,
        v___f_5395_,
    );
    return v___x_5397_;
}
pub unsafe fn l_Lean_Elab_applyVisibility___redArg___lam__4(
    mut v_declName_5398_: *mut leanh::LeanObject,
    mut v___f_5399_: *mut leanh::LeanObject,
    mut v_____do__lift_5400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_declName_5401_ = l_Lean_mkPrivateName(v_____do__lift_5400_, v_declName_5398_);
    v___x_5402_ = leanh::lean_box(0);
    v___x_5403_ = leanh::lean_apply_2(v___f_5399_, v___x_5402_, v_declName_5401_);
    return v___x_5403_;
}
pub unsafe fn l_Lean_Elab_applyVisibility___redArg___lam__4___boxed(
    mut v_declName_5404_: *mut leanh::LeanObject,
    mut v___f_5405_: *mut leanh::LeanObject,
    mut v_____do__lift_5406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5407_ = l_Lean_Elab_applyVisibility___redArg___lam__4(
        v_declName_5404_,
        v___f_5405_,
        v_____do__lift_5406_,
    );
    leanh::lean_dec_ref(v_____do__lift_5406_);
    return v_res_5407_;
}
pub unsafe fn l_Lean_Elab_applyVisibility___redArg___lam__5(
    mut v_modifiers_5408_: *mut leanh::LeanObject,
    mut v_toBind_5409_: *mut leanh::LeanObject,
    mut v_getEnv_5410_: *mut leanh::LeanObject,
    mut v___f_5411_: *mut leanh::LeanObject,
    mut v___f_5412_: *mut leanh::LeanObject,
    mut v_declName_5413_: *mut leanh::LeanObject,
    mut v_____do__lift_5414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_visibility_5415_: u8 = 0;
    let mut v___x_5416_: u8 = 0;
    v_visibility_5415_ = leanh::lean_ctor_get_uint8(
        v_modifiers_5408_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v___x_5416_ = l_Lean_Elab_Visibility_isInferredPublic(v_____do__lift_5414_, v_visibility_5415_);
    if v___x_5416_ == 0 {
        let mut v___x_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_declName_5413_);
        leanh::lean_dec(v___f_5412_);
        v___x_5417_ = leanh::lean_apply_4(
            v_toBind_5409_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_5410_,
            v___f_5411_,
        );
        return v___x_5417_;
    } else {
        let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_5411_);
        leanh::lean_dec(v_getEnv_5410_);
        leanh::lean_dec(v_toBind_5409_);
        v___x_5418_ = leanh::lean_box(0);
        v___x_5419_ = leanh::lean_apply_2(v___f_5412_, v___x_5418_, v_declName_5413_);
        return v___x_5419_;
    }
}
pub unsafe fn l_Lean_Elab_applyVisibility___redArg___lam__5___boxed(
    mut v_modifiers_5420_: *mut leanh::LeanObject,
    mut v_toBind_5421_: *mut leanh::LeanObject,
    mut v_getEnv_5422_: *mut leanh::LeanObject,
    mut v___f_5423_: *mut leanh::LeanObject,
    mut v___f_5424_: *mut leanh::LeanObject,
    mut v_declName_5425_: *mut leanh::LeanObject,
    mut v_____do__lift_5426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5427_ = l_Lean_Elab_applyVisibility___redArg___lam__5(
        v_modifiers_5420_,
        v_toBind_5421_,
        v_getEnv_5422_,
        v___f_5423_,
        v___f_5424_,
        v_declName_5425_,
        v_____do__lift_5426_,
    );
    leanh::lean_dec_ref(v_____do__lift_5426_);
    leanh::lean_dec_ref(v_modifiers_5420_);
    return v_res_5427_;
}
pub unsafe fn l_Lean_Elab_applyVisibility___redArg(
    mut v_inst_5428_: *mut leanh::LeanObject,
    mut v_inst_5429_: *mut leanh::LeanObject,
    mut v_inst_5430_: *mut leanh::LeanObject,
    mut v_inst_5431_: *mut leanh::LeanObject,
    mut v_inst_5432_: *mut leanh::LeanObject,
    mut v_modifiers_5433_: *mut leanh::LeanObject,
    mut v_declName_5434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5435_ = leanh::lean_ctor_get(v_inst_5428_, 0);
    v_toBind_5436_ = leanh::lean_ctor_get(v_inst_5428_, 1);
    leanh::lean_inc_n(v_toBind_5436_, 3);
    v_getEnv_5437_ = leanh::lean_ctor_get(v_inst_5429_, 0);
    leanh::lean_inc_n(v_getEnv_5437_, 2);
    v_modifyEnv_5438_ = leanh::lean_ctor_get(v_inst_5429_, 1);
    leanh::lean_inc(v_modifyEnv_5438_);
    v_toPure_5439_ = leanh::lean_ctor_get(v_toApplicative_5435_, 1);
    leanh::lean_inc(v_toPure_5439_);
    leanh::lean_inc_ref(v_modifiers_5433_);
    v___f_5440_ = leanh::lean_alloc_closure(
        l_Lean_Elab_applyVisibility___redArg___lam__3 as *mut core::ffi::c_void,
        11,
        9,
    );
    leanh::lean_closure_set(v___f_5440_, 0, v_toPure_5439_);
    leanh::lean_closure_set(v___f_5440_, 1, v_modifiers_5433_);
    leanh::lean_closure_set(v___f_5440_, 2, v_modifyEnv_5438_);
    leanh::lean_closure_set(v___f_5440_, 3, v_toBind_5436_);
    leanh::lean_closure_set(v___f_5440_, 4, v_inst_5428_);
    leanh::lean_closure_set(v___f_5440_, 5, v_inst_5429_);
    leanh::lean_closure_set(v___f_5440_, 6, v_inst_5430_);
    leanh::lean_closure_set(v___f_5440_, 7, v_inst_5431_);
    leanh::lean_closure_set(v___f_5440_, 8, v_inst_5432_);
    leanh::lean_inc_ref(v___f_5440_);
    leanh::lean_inc(v_declName_5434_);
    v___f_5441_ = leanh::lean_alloc_closure(
        l_Lean_Elab_applyVisibility___redArg___lam__4___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5441_, 0, v_declName_5434_);
    leanh::lean_closure_set(v___f_5441_, 1, v___f_5440_);
    v___f_5442_ = leanh::lean_alloc_closure(
        l_Lean_Elab_applyVisibility___redArg___lam__5___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_5442_, 0, v_modifiers_5433_);
    leanh::lean_closure_set(v___f_5442_, 1, v_toBind_5436_);
    leanh::lean_closure_set(v___f_5442_, 2, v_getEnv_5437_);
    leanh::lean_closure_set(v___f_5442_, 3, v___f_5441_);
    leanh::lean_closure_set(v___f_5442_, 4, v___f_5440_);
    leanh::lean_closure_set(v___f_5442_, 5, v_declName_5434_);
    v___x_5443_ = leanh::lean_apply_4(
        v_toBind_5436_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_5437_,
        v___f_5442_,
    );
    return v___x_5443_;
}
pub unsafe fn l_Lean_Elab_applyVisibility(
    mut v_m_5444_: *mut leanh::LeanObject,
    mut v_inst_5445_: *mut leanh::LeanObject,
    mut v_inst_5446_: *mut leanh::LeanObject,
    mut v_inst_5447_: *mut leanh::LeanObject,
    mut v_inst_5448_: *mut leanh::LeanObject,
    mut v_inst_5449_: *mut leanh::LeanObject,
    mut v_modifiers_5450_: *mut leanh::LeanObject,
    mut v_declName_5451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5452_ = l_Lean_Elab_applyVisibility___redArg(
        v_inst_5445_,
        v_inst_5446_,
        v_inst_5447_,
        v_inst_5448_,
        v_inst_5449_,
        v_modifiers_5450_,
        v_declName_5451_,
    );
    return v___x_5452_;
}
pub unsafe fn l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0(
    mut v_toPure_5453_: *mut leanh::LeanObject,
    mut v_____s_5454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5455_ = leanh::lean_box(0);
    v___x_5456_ =
        leanh::lean_apply_2(v_toPure_5453_, leanh::lean_box(0), v___x_5455_);
    return v___x_5456_;
}
pub unsafe fn l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1(
    mut v___x_5457_: *mut leanh::LeanObject,
    mut v_toPure_5458_: *mut leanh::LeanObject,
    mut v_r_5459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5460_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5460_, 0, v___x_5457_);
    v___x_5461_ =
        leanh::lean_apply_2(v_toPure_5458_, leanh::lean_box(0), v___x_5460_);
    return v___x_5461_;
}
pub unsafe fn _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5463_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__0;
    v___x_5464_ = l_Lean_stringToMessageData(v___x_5463_);
    return v___x_5464_;
}
pub unsafe fn _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5466_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__2;
    v___x_5467_ = l_Lean_stringToMessageData(v___x_5466_);
    return v___x_5467_;
}
pub unsafe fn _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5469_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__4;
    v___x_5470_ = l_Lean_stringToMessageData(v___x_5469_);
    return v___x_5470_;
}
pub unsafe fn l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2(
    mut v_pre_5471_: *mut leanh::LeanObject,
    mut v_declName_5472_: *mut leanh::LeanObject,
    mut v___x_5473_: *mut leanh::LeanObject,
    mut v_toPure_5474_: *mut leanh::LeanObject,
    mut v_inst_5475_: *mut leanh::LeanObject,
    mut v_inst_5476_: *mut leanh::LeanObject,
    mut v_toBind_5477_: *mut leanh::LeanObject,
    mut v___f_5478_: *mut leanh::LeanObject,
    mut v_a_5479_: *mut leanh::LeanObject,
    mut v_x_5480_: *mut leanh::LeanObject,
    mut v___y_5481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: u8 = 0;
    leanh::lean_inc(v_a_5479_);
    leanh::lean_inc(v_pre_5471_);
    v___x_5482_ = l_Lean_Name_append(v_pre_5471_, v_a_5479_);
    v___x_5483_ = lean_name_eq(v___x_5482_, v_declName_5472_);
    leanh::lean_dec(v___x_5482_);
    if v___x_5483_ == 0 {
        let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_5479_);
        leanh::lean_dec(v___f_5478_);
        leanh::lean_dec(v_toBind_5477_);
        leanh::lean_dec_ref(v_inst_5476_);
        leanh::lean_dec_ref(v_inst_5475_);
        leanh::lean_dec(v_declName_5472_);
        leanh::lean_dec(v_pre_5471_);
        v___x_5484_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5484_, 0, v___x_5473_);
        v___x_5485_ =
            leanh::lean_apply_2(v_toPure_5474_, leanh::lean_box(0), v___x_5484_);
        return v___x_5485_;
    } else {
        let mut v___x_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5487_: u8 = 0;
        let mut v___x_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_5474_);
        v___x_5486_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once
            ),
            _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1,
        );
        v___x_5487_ = 0;
        v___x_5488_ = l_Lean_MessageData_ofConstName(v_declName_5472_, v___x_5487_);
        v___x_5489_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5489_, 0, v___x_5486_);
        leanh::lean_ctor_set(v___x_5489_, 1, v___x_5488_);
        v___x_5490_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once
            ),
            _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3,
        );
        v___x_5491_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5491_, 0, v___x_5489_);
        leanh::lean_ctor_set(v___x_5491_, 1, v___x_5490_);
        v___x_5492_ = l_Lean_MessageData_ofName(v_pre_5471_);
        v___x_5493_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5493_, 0, v___x_5491_);
        leanh::lean_ctor_set(v___x_5493_, 1, v___x_5492_);
        v___x_5494_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once
            ),
            _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5,
        );
        v___x_5495_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5495_, 0, v___x_5493_);
        leanh::lean_ctor_set(v___x_5495_, 1, v___x_5494_);
        v___x_5496_ = l_Lean_MessageData_ofName(v_a_5479_);
        v___x_5497_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5497_, 0, v___x_5495_);
        leanh::lean_ctor_set(v___x_5497_, 1, v___x_5496_);
        v___x_5498_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once
            ),
            _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1,
        );
        v___x_5499_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5499_, 0, v___x_5497_);
        leanh::lean_ctor_set(v___x_5499_, 1, v___x_5498_);
        v___x_5500_ = l_Lean_throwError___redArg(v_inst_5475_, v_inst_5476_, v___x_5499_);
        v___x_5501_ = leanh::lean_apply_4(
            v_toBind_5477_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_5500_,
            v___f_5478_,
        );
        return v___x_5501_;
    }
}
pub unsafe fn l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(
    mut v_pre_5502_: *mut leanh::LeanObject,
    mut v___x_5503_: u8,
    mut v_toPure_5504_: *mut leanh::LeanObject,
    mut v_declName_5505_: *mut leanh::LeanObject,
    mut v_inst_5506_: *mut leanh::LeanObject,
    mut v_inst_5507_: *mut leanh::LeanObject,
    mut v_toBind_5508_: *mut leanh::LeanObject,
    mut v___f_5509_: *mut leanh::LeanObject,
    mut v_____do__lift_5510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fieldNames_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5515_: usize = 0;
    let mut v___x_5516_: usize = 0;
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_pre_5502_);
    v_fieldNames_5511_ =
        l_Lean_getStructureFieldsFlattened(v_____do__lift_5510_, v_pre_5502_, v___x_5503_);
    v___x_5512_ = leanh::lean_box(0);
    leanh::lean_inc(v_toPure_5504_);
    v___f_5513_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5513_, 0, v___x_5512_);
    leanh::lean_closure_set(v___f_5513_, 1, v_toPure_5504_);
    leanh::lean_inc(v_toBind_5508_);
    leanh::lean_inc_ref(v_inst_5506_);
    v___f_5514_ = leanh::lean_alloc_closure(
        l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2 as *mut core::ffi::c_void,
        11,
        8,
    );
    leanh::lean_closure_set(v___f_5514_, 0, v_pre_5502_);
    leanh::lean_closure_set(v___f_5514_, 1, v_declName_5505_);
    leanh::lean_closure_set(v___f_5514_, 2, v___x_5512_);
    leanh::lean_closure_set(v___f_5514_, 3, v_toPure_5504_);
    leanh::lean_closure_set(v___f_5514_, 4, v_inst_5506_);
    leanh::lean_closure_set(v___f_5514_, 5, v_inst_5507_);
    leanh::lean_closure_set(v___f_5514_, 6, v_toBind_5508_);
    leanh::lean_closure_set(v___f_5514_, 7, v___f_5513_);
    v_sz_5515_ = lean_array_size(v_fieldNames_5511_);
    v___x_5516_ = 0usize;
    v___x_5517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_5506_,
        v_fieldNames_5511_,
        v___f_5514_,
        v_sz_5515_,
        v___x_5516_,
        v___x_5512_,
    );
    v___x_5518_ = leanh::lean_apply_4(
        v_toBind_5508_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5517_,
        v___f_5509_,
    );
    return v___x_5518_;
}
pub unsafe fn l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed(
    mut v_pre_5519_: *mut leanh::LeanObject,
    mut v___x_5520_: *mut leanh::LeanObject,
    mut v_toPure_5521_: *mut leanh::LeanObject,
    mut v_declName_5522_: *mut leanh::LeanObject,
    mut v_inst_5523_: *mut leanh::LeanObject,
    mut v_inst_5524_: *mut leanh::LeanObject,
    mut v_toBind_5525_: *mut leanh::LeanObject,
    mut v___f_5526_: *mut leanh::LeanObject,
    mut v_____do__lift_5527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_672__boxed_5528_: u8 = 0;
    let mut v_res_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_672__boxed_5528_ = (leanh::lean_unbox(v___x_5520_) as u8);
    v_res_5529_ = l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3(
        v_pre_5519_,
        v___x_672__boxed_5528_,
        v_toPure_5521_,
        v_declName_5522_,
        v_inst_5523_,
        v_inst_5524_,
        v_toBind_5525_,
        v___f_5526_,
        v_____do__lift_5527_,
    );
    return v_res_5529_;
}
pub unsafe fn l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4(
    mut v_pre_5530_: *mut leanh::LeanObject,
    mut v_toPure_5531_: *mut leanh::LeanObject,
    mut v_declName_5532_: *mut leanh::LeanObject,
    mut v_inst_5533_: *mut leanh::LeanObject,
    mut v_inst_5534_: *mut leanh::LeanObject,
    mut v_toBind_5535_: *mut leanh::LeanObject,
    mut v___f_5536_: *mut leanh::LeanObject,
    mut v_getEnv_5537_: *mut leanh::LeanObject,
    mut v_____do__lift_5538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5539_: u8 = 0;
    leanh::lean_inc(v_pre_5530_);
    v___x_5539_ = l_Lean_isStructure(v_____do__lift_5538_, v_pre_5530_);
    if v___x_5539_ == 0 {
        let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_getEnv_5537_);
        leanh::lean_dec(v___f_5536_);
        leanh::lean_dec(v_toBind_5535_);
        leanh::lean_dec_ref(v_inst_5534_);
        leanh::lean_dec_ref(v_inst_5533_);
        leanh::lean_dec(v_declName_5532_);
        leanh::lean_dec(v_pre_5530_);
        v___x_5540_ = leanh::lean_box(0);
        v___x_5541_ =
            leanh::lean_apply_2(v_toPure_5531_, leanh::lean_box(0), v___x_5540_);
        return v___x_5541_;
    } else {
        let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5542_ = leanh::lean_box((v___x_5539_) as usize);
        leanh::lean_inc(v_toBind_5535_);
        v___f_5543_ = leanh::lean_alloc_closure(
            l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__3___boxed
                as *mut core::ffi::c_void,
            9,
            8,
        );
        leanh::lean_closure_set(v___f_5543_, 0, v_pre_5530_);
        leanh::lean_closure_set(v___f_5543_, 1, v___x_5542_);
        leanh::lean_closure_set(v___f_5543_, 2, v_toPure_5531_);
        leanh::lean_closure_set(v___f_5543_, 3, v_declName_5532_);
        leanh::lean_closure_set(v___f_5543_, 4, v_inst_5533_);
        leanh::lean_closure_set(v___f_5543_, 5, v_inst_5534_);
        leanh::lean_closure_set(v___f_5543_, 6, v_toBind_5535_);
        leanh::lean_closure_set(v___f_5543_, 7, v___f_5536_);
        v___x_5544_ = leanh::lean_apply_4(
            v_toBind_5535_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_5537_,
            v___f_5543_,
        );
        return v___x_5544_;
    }
}
pub unsafe fn l_Lean_Elab_checkIfShadowingStructureField___redArg(
    mut v_inst_5545_: *mut leanh::LeanObject,
    mut v_inst_5546_: *mut leanh::LeanObject,
    mut v_inst_5547_: *mut leanh::LeanObject,
    mut v_declName_5548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_declName_5548_) == 1 {
        let mut v_toApplicative_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_pre_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_5549_ = leanh::lean_ctor_get(v_inst_5545_, 0);
        v_toBind_5550_ = leanh::lean_ctor_get(v_inst_5545_, 1);
        leanh::lean_inc_n(v_toBind_5550_, 2);
        v_toPure_5551_ = leanh::lean_ctor_get(v_toApplicative_5549_, 1);
        leanh::lean_inc_n(v_toPure_5551_, 2);
        v_pre_5552_ = leanh::lean_ctor_get(v_declName_5548_, 0);
        leanh::lean_inc(v_pre_5552_);
        v_getEnv_5553_ = leanh::lean_ctor_get(v_inst_5546_, 0);
        leanh::lean_inc_n(v_getEnv_5553_, 2);
        leanh::lean_dec_ref(v_inst_5546_);
        v___f_5554_ = leanh::lean_alloc_closure(
            l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_5554_, 0, v_toPure_5551_);
        v___f_5555_ = leanh::lean_alloc_closure(
            l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__4 as *mut core::ffi::c_void,
            9,
            8,
        );
        leanh::lean_closure_set(v___f_5555_, 0, v_pre_5552_);
        leanh::lean_closure_set(v___f_5555_, 1, v_toPure_5551_);
        leanh::lean_closure_set(v___f_5555_, 2, v_declName_5548_);
        leanh::lean_closure_set(v___f_5555_, 3, v_inst_5545_);
        leanh::lean_closure_set(v___f_5555_, 4, v_inst_5547_);
        leanh::lean_closure_set(v___f_5555_, 5, v_toBind_5550_);
        leanh::lean_closure_set(v___f_5555_, 6, v___f_5554_);
        leanh::lean_closure_set(v___f_5555_, 7, v_getEnv_5553_);
        v___x_5556_ = leanh::lean_apply_4(
            v_toBind_5550_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_5553_,
            v___f_5555_,
        );
        return v___x_5556_;
    } else {
        let mut v_toApplicative_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_5557_ = leanh::lean_ctor_get(v_inst_5545_, 0);
        leanh::lean_inc_ref(v_toApplicative_5557_);
        leanh::lean_dec(v_declName_5548_);
        leanh::lean_dec_ref(v_inst_5547_);
        leanh::lean_dec_ref(v_inst_5546_);
        leanh::lean_dec_ref(v_inst_5545_);
        v_toPure_5558_ = leanh::lean_ctor_get(v_toApplicative_5557_, 1);
        leanh::lean_inc(v_toPure_5558_);
        leanh::lean_dec_ref(v_toApplicative_5557_);
        v___x_5559_ = leanh::lean_box(0);
        v___x_5560_ =
            leanh::lean_apply_2(v_toPure_5558_, leanh::lean_box(0), v___x_5559_);
        return v___x_5560_;
    }
}
pub unsafe fn l_Lean_Elab_checkIfShadowingStructureField(
    mut v_m_5561_: *mut leanh::LeanObject,
    mut v_inst_5562_: *mut leanh::LeanObject,
    mut v_inst_5563_: *mut leanh::LeanObject,
    mut v_inst_5564_: *mut leanh::LeanObject,
    mut v_declName_5565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5566_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(
        v_inst_5562_,
        v_inst_5563_,
        v_inst_5564_,
        v_declName_5565_,
    );
    return v___x_5566_;
}
pub unsafe fn l_Lean_Elab_mkDeclName___redArg___lam__0(
    mut v_toApplicative_5567_: *mut leanh::LeanObject,
    mut v_declName_5568_: *mut leanh::LeanObject,
    mut v_shortName_5569_: *mut leanh::LeanObject,
    mut v_____r_5570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_5571_ = leanh::lean_ctor_get(v_toApplicative_5567_, 1);
    leanh::lean_inc(v_toPure_5571_);
    leanh::lean_dec_ref(v_toApplicative_5567_);
    v___x_5572_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5572_, 0, v_declName_5568_);
    leanh::lean_ctor_set(v___x_5572_, 1, v_shortName_5569_);
    v___x_5573_ =
        leanh::lean_apply_2(v_toPure_5571_, leanh::lean_box(0), v___x_5572_);
    return v___x_5573_;
}
pub unsafe fn _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5575_ = l_Lean_Elab_mkDeclName___redArg___lam__2___closed__0;
    v___x_5576_ = l_Lean_stringToMessageData(v___x_5575_);
    return v___x_5576_;
}
pub unsafe fn l_Lean_Elab_mkDeclName___redArg___lam__2(
    mut v_modifiers_5577_: *mut leanh::LeanObject,
    mut v_toApplicative_5578_: *mut leanh::LeanObject,
    mut v_shortName_5579_: *mut leanh::LeanObject,
    mut v_currNamespace_5580_: *mut leanh::LeanObject,
    mut v_inst_5581_: *mut leanh::LeanObject,
    mut v_inst_5582_: *mut leanh::LeanObject,
    mut v_toBind_5583_: *mut leanh::LeanObject,
    mut v_declName_5584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isProtected_5585_: u8 = 0;
    v_isProtected_5585_ = leanh::lean_ctor_get_uint8(
        v_modifiers_5577_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
    );
    if v_isProtected_5585_ == 0 {
        let mut v_toPure_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toBind_5583_);
        leanh::lean_dec_ref(v_inst_5582_);
        leanh::lean_dec_ref(v_inst_5581_);
        leanh::lean_dec(v_currNamespace_5580_);
        v_toPure_5586_ = leanh::lean_ctor_get(v_toApplicative_5578_, 1);
        leanh::lean_inc(v_toPure_5586_);
        leanh::lean_dec_ref(v_toApplicative_5578_);
        v___x_5587_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5587_, 0, v_declName_5584_);
        leanh::lean_ctor_set(v___x_5587_, 1, v_shortName_5579_);
        v___x_5588_ =
            leanh::lean_apply_2(v_toPure_5586_, leanh::lean_box(0), v___x_5587_);
        return v___x_5588_;
    } else {
        if leanh::lean_obj_tag(v_currNamespace_5580_) == 1 {
            let mut v_str_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_5583_);
            leanh::lean_dec_ref(v_inst_5582_);
            leanh::lean_dec_ref(v_inst_5581_);
            v_str_5589_ = leanh::lean_ctor_get(v_currNamespace_5580_, 1);
            leanh::lean_inc_ref(v_str_5589_);
            leanh::lean_dec_ref_known(v_currNamespace_5580_, 2);
            v_toPure_5590_ = leanh::lean_ctor_get(v_toApplicative_5578_, 1);
            leanh::lean_inc(v_toPure_5590_);
            leanh::lean_dec_ref(v_toApplicative_5578_);
            v___x_5591_ = leanh::lean_box(0);
            v___x_5592_ = l_Lean_Name_str___override(v___x_5591_, v_str_5589_);
            v___x_5593_ = l_Lean_Name_append(v___x_5592_, v_shortName_5579_);
            v___x_5594_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_5594_, 0, v_declName_5584_);
            leanh::lean_ctor_set(v___x_5594_, 1, v___x_5593_);
            v___x_5595_ =
                leanh::lean_apply_2(v_toPure_5590_, leanh::lean_box(0), v___x_5594_);
            return v___x_5595_;
        } else {
            let mut v___f_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5597_: u8 = 0;
            leanh::lean_dec(v_currNamespace_5580_);
            leanh::lean_inc(v_shortName_5579_);
            leanh::lean_inc(v_declName_5584_);
            leanh::lean_inc_ref(v_toApplicative_5578_);
            v___f_5596_ = leanh::lean_alloc_closure(
                l_Lean_Elab_mkDeclName___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_5596_, 0, v_toApplicative_5578_);
            leanh::lean_closure_set(v___f_5596_, 1, v_declName_5584_);
            leanh::lean_closure_set(v___f_5596_, 2, v_shortName_5579_);
            v___x_5597_ = l_Lean_Name_isAtomic(v_shortName_5579_);
            if v___x_5597_ == 0 {
                let mut v___x_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_5596_);
                leanh::lean_dec(v_toBind_5583_);
                leanh::lean_dec_ref(v_inst_5582_);
                leanh::lean_dec_ref(v_inst_5581_);
                v___x_5598_ = leanh::lean_box(0);
                v___x_5599_ = l_Lean_Elab_mkDeclName___redArg___lam__0(
                    v_toApplicative_5578_,
                    v_declName_5584_,
                    v_shortName_5579_,
                    v___x_5598_,
                );
                return v___x_5599_;
            } else {
                let mut v___f_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_declName_5584_);
                leanh::lean_dec(v_shortName_5579_);
                leanh::lean_dec_ref(v_toApplicative_5578_);
                v___f_5600_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_5600_, 0, v___f_5596_);
                v___x_5601_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once
                    ),
                    _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1,
                );
                v___x_5602_ = l_Lean_throwError___redArg(v_inst_5581_, v_inst_5582_, v___x_5601_);
                v___x_5603_ = leanh::lean_apply_4(
                    v_toBind_5583_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_5602_,
                    v___f_5600_,
                );
                return v___x_5603_;
            }
        }
    }
}
pub unsafe fn l_Lean_Elab_mkDeclName___redArg___lam__2___boxed(
    mut v_modifiers_5604_: *mut leanh::LeanObject,
    mut v_toApplicative_5605_: *mut leanh::LeanObject,
    mut v_shortName_5606_: *mut leanh::LeanObject,
    mut v_currNamespace_5607_: *mut leanh::LeanObject,
    mut v_inst_5608_: *mut leanh::LeanObject,
    mut v_inst_5609_: *mut leanh::LeanObject,
    mut v_toBind_5610_: *mut leanh::LeanObject,
    mut v_declName_5611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5612_ = l_Lean_Elab_mkDeclName___redArg___lam__2(
        v_modifiers_5604_,
        v_toApplicative_5605_,
        v_shortName_5606_,
        v_currNamespace_5607_,
        v_inst_5608_,
        v_inst_5609_,
        v_toBind_5610_,
        v_declName_5611_,
    );
    leanh::lean_dec_ref(v_modifiers_5604_);
    return v_res_5612_;
}
pub unsafe fn l_Lean_Elab_mkDeclName___redArg___lam__1(
    mut v_inst_5613_: *mut leanh::LeanObject,
    mut v_inst_5614_: *mut leanh::LeanObject,
    mut v_inst_5615_: *mut leanh::LeanObject,
    mut v_inst_5616_: *mut leanh::LeanObject,
    mut v_inst_5617_: *mut leanh::LeanObject,
    mut v_modifiers_5618_: *mut leanh::LeanObject,
    mut v___y_5619_: *mut leanh::LeanObject,
    mut v_toBind_5620_: *mut leanh::LeanObject,
    mut v___f_5621_: *mut leanh::LeanObject,
    mut v_____r_5622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5623_ = l_Lean_Elab_applyVisibility___redArg(
        v_inst_5613_,
        v_inst_5614_,
        v_inst_5615_,
        v_inst_5616_,
        v_inst_5617_,
        v_modifiers_5618_,
        v___y_5619_,
    );
    v___x_5624_ = leanh::lean_apply_4(
        v_toBind_5620_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5623_,
        v___f_5621_,
    );
    return v___x_5624_;
}
pub unsafe fn l_Lean_Elab_mkDeclName___redArg___lam__3(
    mut v_modifiers_5625_: *mut leanh::LeanObject,
    mut v_toApplicative_5626_: *mut leanh::LeanObject,
    mut v_inst_5627_: *mut leanh::LeanObject,
    mut v_inst_5628_: *mut leanh::LeanObject,
    mut v_toBind_5629_: *mut leanh::LeanObject,
    mut v_inst_5630_: *mut leanh::LeanObject,
    mut v_inst_5631_: *mut leanh::LeanObject,
    mut v_inst_5632_: *mut leanh::LeanObject,
    mut v___y_5633_: *mut leanh::LeanObject,
    mut v_____r_5634_: *mut leanh::LeanObject,
    mut v_shortName_5635_: *mut leanh::LeanObject,
    mut v_currNamespace_5636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_toBind_5629_, 2);
    leanh::lean_inc_ref_n(v_inst_5628_, 2);
    leanh::lean_inc_ref_n(v_inst_5627_, 2);
    leanh::lean_inc_ref(v_modifiers_5625_);
    v___f_5637_ = leanh::lean_alloc_closure(
        l_Lean_Elab_mkDeclName___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_5637_, 0, v_modifiers_5625_);
    leanh::lean_closure_set(v___f_5637_, 1, v_toApplicative_5626_);
    leanh::lean_closure_set(v___f_5637_, 2, v_shortName_5635_);
    leanh::lean_closure_set(v___f_5637_, 3, v_currNamespace_5636_);
    leanh::lean_closure_set(v___f_5637_, 4, v_inst_5627_);
    leanh::lean_closure_set(v___f_5637_, 5, v_inst_5628_);
    leanh::lean_closure_set(v___f_5637_, 6, v_toBind_5629_);
    leanh::lean_inc(v___y_5633_);
    leanh::lean_inc_ref(v_inst_5630_);
    v___f_5638_ = leanh::lean_alloc_closure(
        l_Lean_Elab_mkDeclName___redArg___lam__1 as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_5638_, 0, v_inst_5627_);
    leanh::lean_closure_set(v___f_5638_, 1, v_inst_5630_);
    leanh::lean_closure_set(v___f_5638_, 2, v_inst_5628_);
    leanh::lean_closure_set(v___f_5638_, 3, v_inst_5631_);
    leanh::lean_closure_set(v___f_5638_, 4, v_inst_5632_);
    leanh::lean_closure_set(v___f_5638_, 5, v_modifiers_5625_);
    leanh::lean_closure_set(v___f_5638_, 6, v___y_5633_);
    leanh::lean_closure_set(v___f_5638_, 7, v_toBind_5629_);
    leanh::lean_closure_set(v___f_5638_, 8, v___f_5637_);
    v___x_5639_ = l_Lean_Elab_checkIfShadowingStructureField___redArg(
        v_inst_5627_,
        v_inst_5630_,
        v_inst_5628_,
        v___y_5633_,
    );
    v___x_5640_ = leanh::lean_apply_4(
        v_toBind_5629_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5639_,
        v___f_5638_,
    );
    return v___x_5640_;
}
pub unsafe fn l_Lean_Elab_mkDeclName___redArg___lam__4(
    mut v___f_5641_: *mut leanh::LeanObject,
    mut v_shortName_5642_: *mut leanh::LeanObject,
    mut v_currNamespace_5643_: *mut leanh::LeanObject,
    mut v_____r_5644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5645_ = leanh::lean_apply_3(
        v___f_5641_,
        v_____r_5644_,
        v_shortName_5642_,
        v_currNamespace_5643_,
    );
    return v___x_5645_;
}
pub unsafe fn l_Lean_Elab_mkDeclName___redArg___lam__5(
    mut v_modifiers_5646_: *mut leanh::LeanObject,
    mut v_toApplicative_5647_: *mut leanh::LeanObject,
    mut v_inst_5648_: *mut leanh::LeanObject,
    mut v_inst_5649_: *mut leanh::LeanObject,
    mut v_toBind_5650_: *mut leanh::LeanObject,
    mut v_inst_5651_: *mut leanh::LeanObject,
    mut v_inst_5652_: *mut leanh::LeanObject,
    mut v_inst_5653_: *mut leanh::LeanObject,
    mut v_isRootName_5654_: u8,
    mut v_shortName_5655_: *mut leanh::LeanObject,
    mut v_currNamespace_5656_: *mut leanh::LeanObject,
    mut v_name_5657_: *mut leanh::LeanObject,
    mut v___x_5658_: *mut leanh::LeanObject,
    mut v_imported_5659_: *mut leanh::LeanObject,
    mut v_ctx_5660_: *mut leanh::LeanObject,
    mut v_scopes_5661_: *mut leanh::LeanObject,
    mut v_____r_5662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shortName_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_isRootName_5654_ == 0 {
                    leanh::lean_dec(v_scopes_5661_);
                    leanh::lean_dec(v_ctx_5660_);
                    leanh::lean_dec(v_imported_5659_);
                    leanh::lean_inc(v_shortName_5655_);
                    leanh::lean_inc(v_currNamespace_5656_);
                    v___x_5683_ = l_Lean_Name_append(v_currNamespace_5656_, v_shortName_5655_);
                    v___y_5664_ = v___x_5683_;
                    state = 1;
                    continue;
                } else {
                    v___x_5684_ = leanh::lean_box(0);
                    leanh::lean_inc(v_name_5657_);
                    v___x_5685_ = l_Lean_Name_replacePrefix(v_name_5657_, v___x_5658_, v___x_5684_);
                    v___x_5686_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_5686_, 0, v___x_5685_);
                    leanh::lean_ctor_set(v___x_5686_, 1, v_imported_5659_);
                    leanh::lean_ctor_set(v___x_5686_, 2, v_ctx_5660_);
                    leanh::lean_ctor_set(v___x_5686_, 3, v_scopes_5661_);
                    v___x_5687_ = l_Lean_MacroScopesView_review(v___x_5686_);
                    v___y_5664_ = v___x_5687_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v___y_5664_);
                leanh::lean_inc_ref(v_inst_5653_);
                leanh::lean_inc(v_inst_5652_);
                leanh::lean_inc_ref(v_inst_5651_);
                leanh::lean_inc(v_toBind_5650_);
                leanh::lean_inc_ref(v_inst_5649_);
                leanh::lean_inc_ref(v_inst_5648_);
                leanh::lean_inc_ref(v_toApplicative_5647_);
                leanh::lean_inc_ref(v_modifiers_5646_);
                v___f_5665_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_mkDeclName___redArg___lam__3 as *mut core::ffi::c_void,
                    12,
                    9,
                );
                leanh::lean_closure_set(v___f_5665_, 0, v_modifiers_5646_);
                leanh::lean_closure_set(v___f_5665_, 1, v_toApplicative_5647_);
                leanh::lean_closure_set(v___f_5665_, 2, v_inst_5648_);
                leanh::lean_closure_set(v___f_5665_, 3, v_inst_5649_);
                leanh::lean_closure_set(v___f_5665_, 4, v_toBind_5650_);
                leanh::lean_closure_set(v___f_5665_, 5, v_inst_5651_);
                leanh::lean_closure_set(v___f_5665_, 6, v_inst_5652_);
                leanh::lean_closure_set(v___f_5665_, 7, v_inst_5653_);
                leanh::lean_closure_set(v___f_5665_, 8, v___y_5664_);
                if v_isRootName_5654_ == 0 {
                    leanh::lean_dec_ref(v___f_5665_);
                    leanh::lean_dec(v_name_5657_);
                    v___x_5666_ = leanh::lean_box(0);
                    v___x_5667_ = l_Lean_Elab_mkDeclName___redArg___lam__3(
                        v_modifiers_5646_,
                        v_toApplicative_5647_,
                        v_inst_5648_,
                        v_inst_5649_,
                        v_toBind_5650_,
                        v_inst_5651_,
                        v_inst_5652_,
                        v_inst_5653_,
                        v___y_5664_,
                        v___x_5666_,
                        v_shortName_5655_,
                        v_currNamespace_5656_,
                    );
                    return v___x_5667_;
                } else {
                    if leanh::lean_obj_tag(v_name_5657_) == 1 {
                        leanh::lean_dec_ref(v___f_5665_);
                        leanh::lean_dec(v_currNamespace_5656_);
                        leanh::lean_dec(v_shortName_5655_);
                        v_pre_5668_ = leanh::lean_ctor_get(v_name_5657_, 0);
                        leanh::lean_inc(v_pre_5668_);
                        v_str_5669_ = leanh::lean_ctor_get(v_name_5657_, 1);
                        leanh::lean_inc_ref(v_str_5669_);
                        leanh::lean_dec_ref_known(v_name_5657_, 2);
                        v___x_5670_ = leanh::lean_box(0);
                        v_shortName_5671_ = l_Lean_Name_str___override(v___x_5670_, v_str_5669_);
                        v_currNamespace_5672_ =
                            l_Lean_Name_replacePrefix(v_pre_5668_, v___x_5658_, v___x_5670_);
                        v___x_5673_ = leanh::lean_box(0);
                        v___x_5674_ = l_Lean_Elab_mkDeclName___redArg___lam__3(
                            v_modifiers_5646_,
                            v_toApplicative_5647_,
                            v_inst_5648_,
                            v_inst_5649_,
                            v_toBind_5650_,
                            v_inst_5651_,
                            v_inst_5652_,
                            v_inst_5653_,
                            v___y_5664_,
                            v___x_5673_,
                            v_shortName_5671_,
                            v_currNamespace_5672_,
                        );
                        return v___x_5674_;
                    } else {
                        leanh::lean_dec(v___y_5664_);
                        leanh::lean_dec_ref(v_inst_5653_);
                        leanh::lean_dec(v_inst_5652_);
                        leanh::lean_dec_ref(v_inst_5651_);
                        leanh::lean_dec_ref(v_toApplicative_5647_);
                        leanh::lean_dec_ref(v_modifiers_5646_);
                        v___f_5675_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_mkDeclName___redArg___lam__4 as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        leanh::lean_closure_set(v___f_5675_, 0, v___f_5665_);
                        leanh::lean_closure_set(v___f_5675_, 1, v_shortName_5655_);
                        leanh::lean_closure_set(v___f_5675_, 2, v_currNamespace_5656_);
                        v___x_5676_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once), _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
                        v___x_5677_ = l_Lean_MessageData_ofName(v_name_5657_);
                        v___x_5678_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5678_, 0, v___x_5676_);
                        leanh::lean_ctor_set(v___x_5678_, 1, v___x_5677_);
                        v___x_5679_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once), _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
                        v___x_5680_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5680_, 0, v___x_5678_);
                        leanh::lean_ctor_set(v___x_5680_, 1, v___x_5679_);
                        v___x_5681_ =
                            l_Lean_throwError___redArg(v_inst_5648_, v_inst_5649_, v___x_5680_);
                        v___x_5682_ = leanh::lean_apply_4(
                            v_toBind_5650_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_5681_,
                            v___f_5675_,
                        );
                        return v___x_5682_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_mkDeclName___redArg___lam__5___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifiers_5688_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_toApplicative_5689_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_inst_5690_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_5691_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_toBind_5692_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_5693_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_inst_5694_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_inst_5695_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_isRootName_5696_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_shortName_5697_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_currNamespace_5698_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_name_5699_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_5700_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_imported_5701_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_ctx_5702_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_scopes_5703_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_____r_5704_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_isRootName_boxed_5705_: u8 = 0;
    let mut v_res_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isRootName_boxed_5705_ = (leanh::lean_unbox(v_isRootName_5696_) as u8);
    v_res_5706_ = l_Lean_Elab_mkDeclName___redArg___lam__5(
        v_modifiers_5688_,
        v_toApplicative_5689_,
        v_inst_5690_,
        v_inst_5691_,
        v_toBind_5692_,
        v_inst_5693_,
        v_inst_5694_,
        v_inst_5695_,
        v_isRootName_boxed_5705_,
        v_shortName_5697_,
        v_currNamespace_5698_,
        v_name_5699_,
        v___x_5700_,
        v_imported_5701_,
        v_ctx_5702_,
        v_scopes_5703_,
        v_____r_5704_,
    );
    leanh::lean_dec(v___x_5700_);
    return v_res_5706_;
}
pub unsafe fn _init_l_Lean_Elab_mkDeclName___redArg___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5711_ = l_Lean_Elab_mkDeclName___redArg___closed__2;
    v___x_5712_ = l_Lean_stringToMessageData(v___x_5711_);
    return v___x_5712_;
}
pub unsafe fn l_Lean_Elab_mkDeclName___redArg(
    mut v_inst_5713_: *mut leanh::LeanObject,
    mut v_inst_5714_: *mut leanh::LeanObject,
    mut v_inst_5715_: *mut leanh::LeanObject,
    mut v_inst_5716_: *mut leanh::LeanObject,
    mut v_inst_5717_: *mut leanh::LeanObject,
    mut v_currNamespace_5718_: *mut leanh::LeanObject,
    mut v_modifiers_5719_: *mut leanh::LeanObject,
    mut v_shortName_5720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_view_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRootName_5729_: u8 = 0;
    let mut v___x_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: u8 = 0;
    leanh::lean_inc_n(v_shortName_5720_, 2);
    v_view_5721_ = l_Lean_extractMacroScopes(v_shortName_5720_);
    v_name_5722_ = leanh::lean_ctor_get(v_view_5721_, 0);
    leanh::lean_inc_n(v_name_5722_, 2);
    v_imported_5723_ = leanh::lean_ctor_get(v_view_5721_, 1);
    leanh::lean_inc_n(v_imported_5723_, 2);
    v_ctx_5724_ = leanh::lean_ctor_get(v_view_5721_, 2);
    leanh::lean_inc_n(v_ctx_5724_, 2);
    v_scopes_5725_ = leanh::lean_ctor_get(v_view_5721_, 3);
    leanh::lean_inc_n(v_scopes_5725_, 2);
    leanh::lean_dec_ref(v_view_5721_);
    v_toApplicative_5726_ = leanh::lean_ctor_get(v_inst_5713_, 0);
    v_toBind_5727_ = leanh::lean_ctor_get(v_inst_5713_, 1);
    leanh::lean_inc_n(v_toBind_5727_, 2);
    v___x_5728_ = l_Lean_Elab_mkDeclName___redArg___closed__1;
    v_isRootName_5729_ = l_Lean_Name_isPrefixOf(v___x_5728_, v_name_5722_);
    v___x_5730_ = leanh::lean_box((v_isRootName_5729_) as usize);
    leanh::lean_inc(v_currNamespace_5718_);
    leanh::lean_inc_ref(v_inst_5717_);
    leanh::lean_inc(v_inst_5716_);
    leanh::lean_inc_ref(v_inst_5714_);
    leanh::lean_inc_ref(v_inst_5715_);
    leanh::lean_inc_ref(v_inst_5713_);
    leanh::lean_inc_ref(v_toApplicative_5726_);
    leanh::lean_inc_ref(v_modifiers_5719_);
    v___f_5731_ = leanh::lean_alloc_closure(
        l_Lean_Elab_mkDeclName___redArg___lam__5___boxed as *mut core::ffi::c_void,
        17,
        16,
    );
    leanh::lean_closure_set(v___f_5731_, 0, v_modifiers_5719_);
    leanh::lean_closure_set(v___f_5731_, 1, v_toApplicative_5726_);
    leanh::lean_closure_set(v___f_5731_, 2, v_inst_5713_);
    leanh::lean_closure_set(v___f_5731_, 3, v_inst_5715_);
    leanh::lean_closure_set(v___f_5731_, 4, v_toBind_5727_);
    leanh::lean_closure_set(v___f_5731_, 5, v_inst_5714_);
    leanh::lean_closure_set(v___f_5731_, 6, v_inst_5716_);
    leanh::lean_closure_set(v___f_5731_, 7, v_inst_5717_);
    leanh::lean_closure_set(v___f_5731_, 8, v___x_5730_);
    leanh::lean_closure_set(v___f_5731_, 9, v_shortName_5720_);
    leanh::lean_closure_set(v___f_5731_, 10, v_currNamespace_5718_);
    leanh::lean_closure_set(v___f_5731_, 11, v_name_5722_);
    leanh::lean_closure_set(v___f_5731_, 12, v___x_5728_);
    leanh::lean_closure_set(v___f_5731_, 13, v_imported_5723_);
    leanh::lean_closure_set(v___f_5731_, 14, v_ctx_5724_);
    leanh::lean_closure_set(v___f_5731_, 15, v_scopes_5725_);
    v___x_5732_ = lean_name_eq(v_name_5722_, v___x_5728_);
    if v___x_5732_ == 0 {
        let mut v___x_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_toApplicative_5726_);
        leanh::lean_dec_ref(v___f_5731_);
        v___x_5733_ = leanh::lean_box(0);
        v___x_5734_ = l_Lean_Elab_mkDeclName___redArg___lam__5(
            v_modifiers_5719_,
            v_toApplicative_5726_,
            v_inst_5713_,
            v_inst_5715_,
            v_toBind_5727_,
            v_inst_5714_,
            v_inst_5716_,
            v_inst_5717_,
            v_isRootName_5729_,
            v_shortName_5720_,
            v_currNamespace_5718_,
            v_name_5722_,
            v___x_5728_,
            v_imported_5723_,
            v_ctx_5724_,
            v_scopes_5725_,
            v___x_5733_,
        );
        return v___x_5734_;
    } else {
        let mut v___f_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_scopes_5725_);
        leanh::lean_dec(v_ctx_5724_);
        leanh::lean_dec(v_imported_5723_);
        leanh::lean_dec(v_name_5722_);
        leanh::lean_dec(v_shortName_5720_);
        leanh::lean_dec_ref(v_modifiers_5719_);
        leanh::lean_dec(v_currNamespace_5718_);
        leanh::lean_dec_ref(v_inst_5717_);
        leanh::lean_dec(v_inst_5716_);
        leanh::lean_dec_ref(v_inst_5714_);
        v___f_5735_ = leanh::lean_alloc_closure(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__5 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_5735_, 0, v___f_5731_);
        v___x_5736_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_mkDeclName___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Elab_mkDeclName___redArg___closed__3_once),
            _init_l_Lean_Elab_mkDeclName___redArg___closed__3,
        );
        v___x_5737_ = l_Lean_throwError___redArg(v_inst_5713_, v_inst_5715_, v___x_5736_);
        v___x_5738_ = leanh::lean_apply_4(
            v_toBind_5727_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_5737_,
            v___f_5735_,
        );
        return v___x_5738_;
    }
}
pub unsafe fn l_Lean_Elab_mkDeclName(
    mut v_m_5739_: *mut leanh::LeanObject,
    mut v_inst_5740_: *mut leanh::LeanObject,
    mut v_inst_5741_: *mut leanh::LeanObject,
    mut v_inst_5742_: *mut leanh::LeanObject,
    mut v_inst_5743_: *mut leanh::LeanObject,
    mut v_inst_5744_: *mut leanh::LeanObject,
    mut v_currNamespace_5745_: *mut leanh::LeanObject,
    mut v_modifiers_5746_: *mut leanh::LeanObject,
    mut v_shortName_5747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5748_ = l_Lean_Elab_mkDeclName___redArg(
        v_inst_5740_,
        v_inst_5741_,
        v_inst_5742_,
        v_inst_5743_,
        v_inst_5744_,
        v_currNamespace_5745_,
        v_modifiers_5746_,
        v_shortName_5747_,
    );
    return v___x_5748_;
}
pub unsafe fn l_Lean_Elab_expandDeclIdCore(
    mut v_declId_5758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5759_: u8 = 0;
    v___x_5759_ = l_Lean_Syntax_isIdent(v_declId_5758_);
    if v___x_5759_ == 0 {
        let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_id_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_optUnivDeclStx_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5760_ = leanh::lean_unsigned_to_nat(0);
        v___x_5761_ = l_Lean_Syntax_getArg(v_declId_5758_, v___x_5760_);
        v_id_5762_ = l_Lean_Syntax_getId(v___x_5761_);
        leanh::lean_dec(v___x_5761_);
        v___x_5763_ = leanh::lean_unsigned_to_nat(1);
        v_optUnivDeclStx_5764_ = l_Lean_Syntax_getArg(v_declId_5758_, v___x_5763_);
        v___x_5765_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5765_, 0, v_id_5762_);
        leanh::lean_ctor_set(v___x_5765_, 1, v_optUnivDeclStx_5764_);
        return v___x_5765_;
    } else {
        let mut v___x_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5766_ = l_Lean_Syntax_getId(v_declId_5758_);
        v___x_5767_ = l_Lean_Elab_expandDeclIdCore___closed__3;
        v___x_5768_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5768_, 0, v___x_5766_);
        leanh::lean_ctor_set(v___x_5768_, 1, v___x_5767_);
        return v___x_5768_;
    }
}
pub unsafe fn l_Lean_Elab_expandDeclIdCore___boxed(
    mut v_declId_5769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5770_ = l_Lean_Elab_expandDeclIdCore(v_declId_5769_);
    leanh::lean_dec(v_declId_5769_);
    return v_res_5770_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(
    mut v_msgData_5771_: *mut leanh::LeanObject,
    mut v___y_5772_: *mut leanh::LeanObject,
    mut v___y_5773_: *mut leanh::LeanObject,
    mut v___y_5774_: *mut leanh::LeanObject,
    mut v___y_5775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5777_ = lean_st_ref_get(v___y_5775_);
    v_env_5778_ = leanh::lean_ctor_get(v___x_5777_, 0);
    leanh::lean_inc_ref(v_env_5778_);
    leanh::lean_dec(v___x_5777_);
    v___x_5779_ = lean_st_ref_get(v___y_5773_);
    v_mctx_5780_ = leanh::lean_ctor_get(v___x_5779_, 0);
    leanh::lean_inc_ref(v_mctx_5780_);
    leanh::lean_dec(v___x_5779_);
    v_lctx_5781_ = leanh::lean_ctor_get(v___y_5772_, 2);
    v_options_5782_ = leanh::lean_ctor_get(v___y_5774_, 2);
    leanh::lean_inc_ref(v_options_5782_);
    leanh::lean_inc_ref(v_lctx_5781_);
    v___x_5783_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_5783_, 0, v_env_5778_);
    leanh::lean_ctor_set(v___x_5783_, 1, v_mctx_5780_);
    leanh::lean_ctor_set(v___x_5783_, 2, v_lctx_5781_);
    leanh::lean_ctor_set(v___x_5783_, 3, v_options_5782_);
    v___x_5784_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5784_, 0, v___x_5783_);
    leanh::lean_ctor_set(v___x_5784_, 1, v_msgData_5771_);
    v___x_5785_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5785_, 0, v___x_5784_);
    return v___x_5785_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_5786_: *mut leanh::LeanObject,
    mut v___y_5787_: *mut leanh::LeanObject,
    mut v___y_5788_: *mut leanh::LeanObject,
    mut v___y_5789_: *mut leanh::LeanObject,
    mut v___y_5790_: *mut leanh::LeanObject,
    mut v___y_5791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5792_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msgData_5786_, v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_);
    leanh::lean_dec(v___y_5790_);
    leanh::lean_dec_ref(v___y_5789_);
    leanh::lean_dec(v___y_5788_);
    leanh::lean_dec_ref(v___y_5787_);
    return v_res_5792_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(
    mut v_opts_5793_: *mut leanh::LeanObject,
    mut v_opt_5794_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_5795_ = leanh::lean_ctor_get(v_opt_5794_, 0);
    v_defValue_5796_ = leanh::lean_ctor_get(v_opt_5794_, 1);
    v_map_5797_ = leanh::lean_ctor_get(v_opts_5793_, 0);
    v___x_5798_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5797_,
            v_name_5795_,
        );
    if leanh::lean_obj_tag(v___x_5798_) == 0 {
        let mut v___x_5799_: u8 = 0;
        v___x_5799_ = (leanh::lean_unbox(v_defValue_5796_) as u8);
        return v___x_5799_;
    } else {
        let mut v_val_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5800_ = leanh::lean_ctor_get(v___x_5798_, 0);
        leanh::lean_inc(v_val_5800_);
        leanh::lean_dec_ref_known(v___x_5798_, 1);
        if leanh::lean_obj_tag(v_val_5800_) == 1 {
            let mut v_v_5801_: u8 = 0;
            v_v_5801_ = leanh::lean_ctor_get_uint8(v_val_5800_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_5800_, 0);
            return v_v_5801_;
        } else {
            let mut v___x_5802_: u8 = 0;
            leanh::lean_dec(v_val_5800_);
            v___x_5802_ = (leanh::lean_unbox(v_defValue_5796_) as u8);
            return v___x_5802_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7___boxed(
    mut v_opts_5803_: *mut leanh::LeanObject,
    mut v_opt_5804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5805_: u8 = 0;
    let mut v_r_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5805_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_opts_5803_, v_opt_5804_);
    leanh::lean_dec_ref(v_opt_5804_);
    leanh::lean_dec_ref(v_opts_5803_);
    v_r_5806_ = leanh::lean_box((v_res_5805_) as usize);
    return v_r_5806_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5807_ = leanh::lean_box(1);
    v___x_5808_ = l_Lean_MessageData_ofFormat(v___x_5807_);
    return v___x_5808_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5812_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__2;
    v___x_5813_ = l_Lean_MessageData_ofFormat(v___x_5812_);
    return v___x_5813_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(
    mut v_x_5814_: *mut leanh::LeanObject,
    mut v_x_5815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5820_: u8 = 0;
    let mut v_before_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5824_: u8 = 0;
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5837_: u8 = 0;
    let mut v_unused_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5815_) == 0 {
                    return v_x_5814_;
                } else {
                    v_head_5816_ = leanh::lean_ctor_get(v_x_5815_, 0);
                    v_tail_5817_ = leanh::lean_ctor_get(v_x_5815_, 1);
                    v_isSharedCheck_5839_ = (!leanh::lean_is_exclusive(v_x_5815_)) as u8;
                    if v_isSharedCheck_5839_ == 0 {
                        v___x_5819_ = v_x_5815_;
                        v_isShared_5820_ = v_isSharedCheck_5839_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5817_);
                        leanh::lean_inc(v_head_5816_);
                        leanh::lean_dec(v_x_5815_);
                        v___x_5819_ = leanh::lean_box(0);
                        v_isShared_5820_ = v_isSharedCheck_5839_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_5821_ = leanh::lean_ctor_get(v_head_5816_, 0);
                v_isSharedCheck_5837_ = (!leanh::lean_is_exclusive(v_head_5816_)) as u8;
                if v_isSharedCheck_5837_ == 0 {
                    v_unused_5838_ = leanh::lean_ctor_get(v_head_5816_, 1);
                    leanh::lean_dec(v_unused_5838_);
                    v___x_5823_ = v_head_5816_;
                    v_isShared_5824_ = v_isSharedCheck_5837_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_5821_);
                    leanh::lean_dec(v_head_5816_);
                    v___x_5823_ = leanh::lean_box(0);
                    v_isShared_5824_ = v_isSharedCheck_5837_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5825_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
                if v_isShared_5824_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5823_, 7);
                    leanh::lean_ctor_set(v___x_5823_, 1, v___x_5825_);
                    leanh::lean_ctor_set(v___x_5823_, 0, v_x_5814_);
                    v___x_5827_ = v___x_5823_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5836_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_x_5814_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5836_, 1, v___x_5825_);
                    v___x_5827_ = v_reuseFailAlloc_5836_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5828_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__3);
                if v_isShared_5820_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5819_, 7);
                    leanh::lean_ctor_set(v___x_5819_, 1, v___x_5828_);
                    leanh::lean_ctor_set(v___x_5819_, 0, v___x_5827_);
                    v___x_5830_ = v___x_5819_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5835_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5835_, 0, v___x_5827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5835_, 1, v___x_5828_);
                    v___x_5830_ = v_reuseFailAlloc_5835_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5831_ = l_Lean_MessageData_ofSyntax(v_before_5821_);
                v___x_5832_ = l_Lean_indentD(v___x_5831_);
                v___x_5833_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5833_, 0, v___x_5830_);
                leanh::lean_ctor_set(v___x_5833_, 1, v___x_5832_);
                v_x_5814_ = v___x_5833_;
                v_x_5815_ = v_tail_5817_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5843_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__1;
    v___x_5844_ = l_Lean_MessageData_ofFormat(v___x_5843_);
    return v___x_5844_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(
    mut v_msgData_5845_: *mut leanh::LeanObject,
    mut v_macroStack_5846_: *mut leanh::LeanObject,
    mut v___y_5847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: u8 = 0;
    let mut v___x_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5858_: u8 = 0;
    let mut v___x_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5870_: u8 = 0;
    let mut v_unused_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5849_ = leanh::lean_ctor_get(v___y_5847_, 2);
                v___x_5850_ = l_Lean_Elab_pp_macroStack;
                v___x_5851_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__7(v_options_5849_, v___x_5850_);
                if v___x_5851_ == 0 {
                    leanh::lean_dec(v_macroStack_5846_);
                    v___x_5852_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5852_, 0, v_msgData_5845_);
                    return v___x_5852_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_5846_) == 0 {
                        v___x_5853_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5853_, 0, v_msgData_5845_);
                        return v___x_5853_;
                    } else {
                        v_head_5854_ = leanh::lean_ctor_get(v_macroStack_5846_, 0);
                        leanh::lean_inc(v_head_5854_);
                        v_after_5855_ = leanh::lean_ctor_get(v_head_5854_, 1);
                        v_isSharedCheck_5870_ =
                            (!leanh::lean_is_exclusive(v_head_5854_)) as u8;
                        if v_isSharedCheck_5870_ == 0 {
                            v_unused_5871_ = leanh::lean_ctor_get(v_head_5854_, 0);
                            leanh::lean_dec(v_unused_5871_);
                            v___x_5857_ = v_head_5854_;
                            v_isShared_5858_ = v_isSharedCheck_5870_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_5855_);
                            leanh::lean_dec(v_head_5854_);
                            v___x_5857_ = leanh::lean_box(0);
                            v_isShared_5858_ = v_isSharedCheck_5870_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5859_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8___closed__0);
                if v_isShared_5858_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5857_, 7);
                    leanh::lean_ctor_set(v___x_5857_, 1, v___x_5859_);
                    leanh::lean_ctor_set(v___x_5857_, 0, v_msgData_5845_);
                    v___x_5861_ = v___x_5857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5869_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_msgData_5845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5869_, 1, v___x_5859_);
                    v___x_5861_ = v_reuseFailAlloc_5869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5862_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___closed__2);
                v___x_5863_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5863_, 0, v___x_5861_);
                leanh::lean_ctor_set(v___x_5863_, 1, v___x_5862_);
                v___x_5864_ = l_Lean_MessageData_ofSyntax(v_after_5855_);
                v___x_5865_ = l_Lean_indentD(v___x_5864_);
                v_msgData_5866_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_5866_, 0, v___x_5863_);
                leanh::lean_ctor_set(v_msgData_5866_, 1, v___x_5865_);
                v___x_5867_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3_spec__8(v_msgData_5866_, v_macroStack_5846_);
                v___x_5868_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5868_, 0, v___x_5867_);
                return v___x_5868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_msgData_5872_: *mut leanh::LeanObject,
    mut v_macroStack_5873_: *mut leanh::LeanObject,
    mut v___y_5874_: *mut leanh::LeanObject,
    mut v___y_5875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5876_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_5872_, v_macroStack_5873_, v___y_5874_);
    leanh::lean_dec_ref(v___y_5874_);
    return v_res_5876_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(
    mut v_msg_5877_: *mut leanh::LeanObject,
    mut v___y_5878_: *mut leanh::LeanObject,
    mut v___y_5879_: *mut leanh::LeanObject,
    mut v___y_5880_: *mut leanh::LeanObject,
    mut v___y_5881_: *mut leanh::LeanObject,
    mut v___y_5882_: *mut leanh::LeanObject,
    mut v___y_5883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5894_: u8 = 0;
    let mut v___x_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5899_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5885_ = leanh::lean_ctor_get(v___y_5882_, 5);
                v___x_5886_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__2(v_msg_5877_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_);
                v_a_5887_ = leanh::lean_ctor_get(v___x_5886_, 0);
                leanh::lean_inc(v_a_5887_);
                leanh::lean_dec_ref(v___x_5886_);
                v_macroStack_5888_ = leanh::lean_ctor_get(v___y_5878_, 1);
                v___x_5889_ = l_Lean_Elab_getBetterRef(v_ref_5885_, v_macroStack_5888_);
                leanh::lean_inc(v_macroStack_5888_);
                v___x_5890_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_a_5887_, v_macroStack_5888_, v___y_5882_);
                v_a_5891_ = leanh::lean_ctor_get(v___x_5890_, 0);
                v_isSharedCheck_5899_ = (!leanh::lean_is_exclusive(v___x_5890_)) as u8;
                if v_isSharedCheck_5899_ == 0 {
                    v___x_5893_ = v___x_5890_;
                    v_isShared_5894_ = v_isSharedCheck_5899_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5891_);
                    leanh::lean_dec(v___x_5890_);
                    v___x_5893_ = leanh::lean_box(0);
                    v_isShared_5894_ = v_isSharedCheck_5899_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5895_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5895_, 0, v___x_5889_);
                leanh::lean_ctor_set(v___x_5895_, 1, v_a_5891_);
                if v_isShared_5894_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5893_, 1);
                    leanh::lean_ctor_set(v___x_5893_, 0, v___x_5895_);
                    v___x_5897_ = v___x_5893_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5898_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5898_, 0, v___x_5895_);
                    v___x_5897_ = v_reuseFailAlloc_5898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg___boxed(
    mut v_msg_5900_: *mut leanh::LeanObject,
    mut v___y_5901_: *mut leanh::LeanObject,
    mut v___y_5902_: *mut leanh::LeanObject,
    mut v___y_5903_: *mut leanh::LeanObject,
    mut v___y_5904_: *mut leanh::LeanObject,
    mut v___y_5905_: *mut leanh::LeanObject,
    mut v___y_5906_: *mut leanh::LeanObject,
    mut v___y_5907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5908_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_);
    leanh::lean_dec(v___y_5906_);
    leanh::lean_dec_ref(v___y_5905_);
    leanh::lean_dec(v___y_5904_);
    leanh::lean_dec_ref(v___y_5903_);
    leanh::lean_dec(v___y_5902_);
    leanh::lean_dec_ref(v___y_5901_);
    return v_res_5908_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(
    mut v_env_5909_: *mut leanh::LeanObject,
    mut v_declName_5910_: *mut leanh::LeanObject,
    mut v___f_5911_: *mut leanh::LeanObject,
    mut v_addInfo_5912_: *mut leanh::LeanObject,
    mut v_____r_5913_: *mut leanh::LeanObject,
    mut v___y_5914_: *mut leanh::LeanObject,
    mut v___y_5915_: *mut leanh::LeanObject,
    mut v___y_5916_: *mut leanh::LeanObject,
    mut v___y_5917_: *mut leanh::LeanObject,
    mut v___y_5918_: *mut leanh::LeanObject,
    mut v___y_5919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: u8 = 0;
    let mut v___x_5923_: u8 = 0;
    leanh::lean_inc(v_declName_5910_);
    v___x_5921_ = l_Lean_mkPrivateName(v_env_5909_, v_declName_5910_);
    v___x_5922_ = 1;
    leanh::lean_inc(v___x_5921_);
    v___x_5923_ = l_Lean_Environment_contains(v_env_5909_, v___x_5921_, v___x_5922_);
    if v___x_5923_ == 0 {
        let mut v___x_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_5921_);
        leanh::lean_dec_ref(v_addInfo_5912_);
        leanh::lean_dec(v_declName_5910_);
        v___x_5924_ = leanh::lean_box(0);
        leanh::lean_inc(v___y_5919_);
        leanh::lean_inc_ref(v___y_5918_);
        leanh::lean_inc(v___y_5917_);
        leanh::lean_inc_ref(v___y_5916_);
        leanh::lean_inc(v___y_5915_);
        leanh::lean_inc_ref(v___y_5914_);
        v___x_5925_ = leanh::lean_apply_8(
            v___f_5911_,
            v___x_5924_,
            v___y_5914_,
            v___y_5915_,
            v___y_5916_,
            v___y_5917_,
            v___y_5918_,
            v___y_5919_,
            leanh::lean_box(0),
        );
        return v___x_5925_;
    } else {
        let mut v___x_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___f_5911_);
        leanh::lean_inc(v___y_5919_);
        leanh::lean_inc_ref(v___y_5918_);
        leanh::lean_inc(v___y_5917_);
        leanh::lean_inc_ref(v___y_5916_);
        leanh::lean_inc(v___y_5915_);
        leanh::lean_inc_ref(v___y_5914_);
        v___x_5926_ = leanh::lean_apply_8(
            v_addInfo_5912_,
            v___x_5921_,
            v___y_5914_,
            v___y_5915_,
            v___y_5916_,
            v___y_5917_,
            v___y_5918_,
            v___y_5919_,
            leanh::lean_box(0),
        );
        if leanh::lean_obj_tag(v___x_5926_) == 0 {
            let mut v___x_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_5926_, 1);
            v___x_5927_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1_once
                ),
                _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__6___closed__1,
            );
            v___x_5928_ = l_Lean_MessageData_ofConstName(v_declName_5910_, v___x_5922_);
            v___x_5929_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_5929_, 0, v___x_5927_);
            leanh::lean_ctor_set(v___x_5929_, 1, v___x_5928_);
            v___x_5930_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once
                ),
                _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3,
            );
            v___x_5931_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_5931_, 0, v___x_5929_);
            leanh::lean_ctor_set(v___x_5931_, 1, v___x_5930_);
            v___x_5932_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_5931_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_);
            return v___x_5932_;
        } else {
            leanh::lean_dec(v_declName_5910_);
            return v___x_5926_;
        }
    }
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed(
    mut v_env_5933_: *mut leanh::LeanObject,
    mut v_declName_5934_: *mut leanh::LeanObject,
    mut v___f_5935_: *mut leanh::LeanObject,
    mut v_addInfo_5936_: *mut leanh::LeanObject,
    mut v_____r_5937_: *mut leanh::LeanObject,
    mut v___y_5938_: *mut leanh::LeanObject,
    mut v___y_5939_: *mut leanh::LeanObject,
    mut v___y_5940_: *mut leanh::LeanObject,
    mut v___y_5941_: *mut leanh::LeanObject,
    mut v___y_5942_: *mut leanh::LeanObject,
    mut v___y_5943_: *mut leanh::LeanObject,
    mut v___y_5944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5945_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2(v_env_5933_, v_declName_5934_, v___f_5935_, v_addInfo_5936_, v_____r_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_, v___y_5943_);
    leanh::lean_dec(v___y_5943_);
    leanh::lean_dec_ref(v___y_5942_);
    leanh::lean_dec(v___y_5941_);
    leanh::lean_dec_ref(v___y_5940_);
    leanh::lean_dec(v___y_5939_);
    leanh::lean_dec_ref(v___y_5938_);
    return v_res_5945_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(
    mut v___f_5946_: *mut leanh::LeanObject,
    mut v_declName_5947_: *mut leanh::LeanObject,
    mut v___x_5948_: u8,
    mut v_env_5949_: *mut leanh::LeanObject,
    mut v_____do__lift_5950_: *mut leanh::LeanObject,
    mut v___y_5951_: *mut leanh::LeanObject,
    mut v___y_5952_: *mut leanh::LeanObject,
    mut v___y_5953_: *mut leanh::LeanObject,
    mut v___y_5954_: *mut leanh::LeanObject,
    mut v___y_5955_: *mut leanh::LeanObject,
    mut v___y_5956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5959_: u8 = 0;
    let mut v___x_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: u8 = 0;
    let mut v___x_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_5947_);
                v___x_5968_ = l_Lean_privateToUserName(v_declName_5947_);
                leanh::lean_inc_ref(v_env_5949_);
                v___x_5969_ = lean_is_reserved_name(v_env_5949_, v___x_5968_);
                if v___x_5969_ == 0 {
                    leanh::lean_inc(v_declName_5947_);
                    v___x_5970_ = l_Lean_mkPrivateName(v_____do__lift_5950_, v_declName_5947_);
                    v___x_5971_ = lean_is_reserved_name(v_env_5949_, v___x_5970_);
                    v___y_5959_ = v___x_5971_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_env_5949_);
                    v___y_5959_ = v___x_5969_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_5959_ == 0 {
                    leanh::lean_dec(v_declName_5947_);
                    v___x_5960_ = leanh::lean_box(0);
                    leanh::lean_inc(v___y_5956_);
                    leanh::lean_inc_ref(v___y_5955_);
                    leanh::lean_inc(v___y_5954_);
                    leanh::lean_inc_ref(v___y_5953_);
                    leanh::lean_inc(v___y_5952_);
                    leanh::lean_inc_ref(v___y_5951_);
                    v___x_5961_ = leanh::lean_apply_8(
                        v___f_5946_,
                        v___x_5960_,
                        v___y_5951_,
                        v___y_5952_,
                        v___y_5953_,
                        v___y_5954_,
                        v___y_5955_,
                        v___y_5956_,
                        leanh::lean_box(0),
                    );
                    return v___x_5961_;
                } else {
                    leanh::lean_dec_ref(v___f_5946_);
                    v___x_5962_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once
                        ),
                        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1,
                    );
                    v___x_5963_ = l_Lean_MessageData_ofConstName(v_declName_5947_, v___x_5948_);
                    v___x_5964_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5964_, 0, v___x_5962_);
                    leanh::lean_ctor_set(v___x_5964_, 1, v___x_5963_);
                    v___x_5965_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3_once
                        ),
                        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__3,
                    );
                    v___x_5966_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5966_, 0, v___x_5964_);
                    leanh::lean_ctor_set(v___x_5966_, 1, v___x_5965_);
                    v___x_5967_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_5966_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_);
                    return v___x_5967_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed(
    mut v___f_5972_: *mut leanh::LeanObject,
    mut v_declName_5973_: *mut leanh::LeanObject,
    mut v___x_5974_: *mut leanh::LeanObject,
    mut v_env_5975_: *mut leanh::LeanObject,
    mut v_____do__lift_5976_: *mut leanh::LeanObject,
    mut v___y_5977_: *mut leanh::LeanObject,
    mut v___y_5978_: *mut leanh::LeanObject,
    mut v___y_5979_: *mut leanh::LeanObject,
    mut v___y_5980_: *mut leanh::LeanObject,
    mut v___y_5981_: *mut leanh::LeanObject,
    mut v___y_5982_: *mut leanh::LeanObject,
    mut v___y_5983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_17521__boxed_5984_: u8 = 0;
    let mut v_res_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_17521__boxed_5984_ = (leanh::lean_unbox(v___x_5974_) as u8);
    v_res_5985_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3(v___f_5972_, v_declName_5973_, v___x_17521__boxed_5984_, v_env_5975_, v_____do__lift_5976_, v___y_5977_, v___y_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_);
    leanh::lean_dec(v___y_5982_);
    leanh::lean_dec_ref(v___y_5981_);
    leanh::lean_dec(v___y_5980_);
    leanh::lean_dec_ref(v___y_5979_);
    leanh::lean_dec(v___y_5978_);
    leanh::lean_dec_ref(v___y_5977_);
    leanh::lean_dec_ref(v_____do__lift_5976_);
    return v_res_5985_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(
    mut v_t_5986_: *mut leanh::LeanObject,
    mut v___y_5987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5991_: u8 = 0;
    let mut v___x_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6006_: u8 = 0;
    let mut v_enabled_6007_: u8 = 0;
    let mut v_assignment_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6013_: u8 = 0;
    let mut v___x_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6024_: u8 = 0;
    let mut v_isSharedCheck_6025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5989_ = lean_st_ref_get(v___y_5987_);
                v_infoState_5990_ = leanh::lean_ctor_get(v___x_5989_, 7);
                leanh::lean_inc_ref(v_infoState_5990_);
                leanh::lean_dec(v___x_5989_);
                v_enabled_5991_ = leanh::lean_ctor_get_uint8(
                    v_infoState_5990_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_5990_);
                if v_enabled_5991_ == 0 {
                    leanh::lean_dec_ref(v_t_5986_);
                    v___x_5992_ = leanh::lean_box(0);
                    v___x_5993_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5993_, 0, v___x_5992_);
                    return v___x_5993_;
                } else {
                    v___x_5994_ = lean_st_ref_take(v___y_5987_);
                    v_infoState_5995_ = leanh::lean_ctor_get(v___x_5994_, 7);
                    v_env_5996_ = leanh::lean_ctor_get(v___x_5994_, 0);
                    v_nextMacroScope_5997_ = leanh::lean_ctor_get(v___x_5994_, 1);
                    v_ngen_5998_ = leanh::lean_ctor_get(v___x_5994_, 2);
                    v_auxDeclNGen_5999_ = leanh::lean_ctor_get(v___x_5994_, 3);
                    v_traceState_6000_ = leanh::lean_ctor_get(v___x_5994_, 4);
                    v_cache_6001_ = leanh::lean_ctor_get(v___x_5994_, 5);
                    v_messages_6002_ = leanh::lean_ctor_get(v___x_5994_, 6);
                    v_snapshotTasks_6003_ = leanh::lean_ctor_get(v___x_5994_, 8);
                    v_isSharedCheck_6025_ = (!leanh::lean_is_exclusive(v___x_5994_)) as u8;
                    if v_isSharedCheck_6025_ == 0 {
                        v___x_6005_ = v___x_5994_;
                        v_isShared_6006_ = v_isSharedCheck_6025_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_6003_);
                        leanh::lean_inc(v_infoState_5995_);
                        leanh::lean_inc(v_messages_6002_);
                        leanh::lean_inc(v_cache_6001_);
                        leanh::lean_inc(v_traceState_6000_);
                        leanh::lean_inc(v_auxDeclNGen_5999_);
                        leanh::lean_inc(v_ngen_5998_);
                        leanh::lean_inc(v_nextMacroScope_5997_);
                        leanh::lean_inc(v_env_5996_);
                        leanh::lean_dec(v___x_5994_);
                        v___x_6005_ = leanh::lean_box(0);
                        v_isShared_6006_ = v_isSharedCheck_6025_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_6007_ = leanh::lean_ctor_get_uint8(
                    v_infoState_5995_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_6008_ = leanh::lean_ctor_get(v_infoState_5995_, 0);
                v_lazyAssignment_6009_ = leanh::lean_ctor_get(v_infoState_5995_, 1);
                v_trees_6010_ = leanh::lean_ctor_get(v_infoState_5995_, 2);
                v_isSharedCheck_6024_ = (!leanh::lean_is_exclusive(v_infoState_5995_)) as u8;
                if v_isSharedCheck_6024_ == 0 {
                    v___x_6012_ = v_infoState_5995_;
                    v_isShared_6013_ = v_isSharedCheck_6024_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_trees_6010_);
                    leanh::lean_inc(v_lazyAssignment_6009_);
                    leanh::lean_inc(v_assignment_6008_);
                    leanh::lean_dec(v_infoState_5995_);
                    v___x_6012_ = leanh::lean_box(0);
                    v_isShared_6013_ = v_isSharedCheck_6024_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6014_ = l_Lean_PersistentArray_push___redArg(v_trees_6010_, v_t_5986_);
                if v_isShared_6013_ == 0 {
                    leanh::lean_ctor_set(v___x_6012_, 2, v___x_6014_);
                    v___x_6016_ = v___x_6012_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6023_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_assignment_6008_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6023_, 1, v_lazyAssignment_6009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6023_, 2, v___x_6014_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6023_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_6007_,
                    );
                    v___x_6016_ = v_reuseFailAlloc_6023_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6006_ == 0 {
                    leanh::lean_ctor_set(v___x_6005_, 7, v___x_6016_);
                    v___x_6018_ = v___x_6005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6022_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_env_5996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 1, v_nextMacroScope_5997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 2, v_ngen_5998_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 3, v_auxDeclNGen_5999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 4, v_traceState_6000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 5, v_cache_6001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 6, v_messages_6002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 7, v___x_6016_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 8, v_snapshotTasks_6003_);
                    v___x_6018_ = v_reuseFailAlloc_6022_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6019_ = lean_st_ref_set(v___y_5987_, v___x_6018_);
                v___x_6020_ = leanh::lean_box(0);
                v___x_6021_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6021_, 0, v___x_6020_);
                return v___x_6021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg___boxed(
    mut v_t_6026_: *mut leanh::LeanObject,
    mut v___y_6027_: *mut leanh::LeanObject,
    mut v___y_6028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6029_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_6026_, v___y_6027_);
    leanh::lean_dec(v___y_6027_);
    return v_res_6029_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6030_ = leanh::lean_unsigned_to_nat(32);
    v___x_6031_ = lean_mk_empty_array_with_capacity(v___x_6030_);
    v___x_6032_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6032_, 0, v___x_6031_);
    return v___x_6032_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6033_: usize = 0;
    let mut v___x_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6033_ = 5usize;
    v___x_6034_ = leanh::lean_unsigned_to_nat(0);
    v___x_6035_ = leanh::lean_unsigned_to_nat(32);
    v___x_6036_ = lean_mk_empty_array_with_capacity(v___x_6035_);
    v___x_6037_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__0);
    v___x_6038_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_6038_, 0, v___x_6037_);
    leanh::lean_ctor_set(v___x_6038_, 1, v___x_6036_);
    leanh::lean_ctor_set(v___x_6038_, 2, v___x_6034_);
    leanh::lean_ctor_set(v___x_6038_, 3, v___x_6034_);
    leanh::lean_ctor_set_usize(v___x_6038_, 4, v___x_6033_);
    return v___x_6038_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(
    mut v_t_6039_: *mut leanh::LeanObject,
    mut v___y_6040_: *mut leanh::LeanObject,
    mut v___y_6041_: *mut leanh::LeanObject,
    mut v___y_6042_: *mut leanh::LeanObject,
    mut v___y_6043_: *mut leanh::LeanObject,
    mut v___y_6044_: *mut leanh::LeanObject,
    mut v___y_6045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6049_: u8 = 0;
    v___x_6047_ = lean_st_ref_get(v___y_6045_);
    v_infoState_6048_ = leanh::lean_ctor_get(v___x_6047_, 7);
    leanh::lean_inc_ref(v_infoState_6048_);
    leanh::lean_dec(v___x_6047_);
    v_enabled_6049_ = leanh::lean_ctor_get_uint8(
        v_infoState_6048_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    leanh::lean_dec_ref(v_infoState_6048_);
    if v_enabled_6049_ == 0 {
        let mut v___x_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_t_6039_);
        v___x_6050_ = leanh::lean_box(0);
        v___x_6051_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6051_, 0, v___x_6050_);
        return v___x_6051_;
    } else {
        let mut v___x_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6052_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___closed__1);
        v___x_6053_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_6053_, 0, v_t_6039_);
        leanh::lean_ctor_set(v___x_6053_, 1, v___x_6052_);
        v___x_6054_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v___x_6053_, v___y_6045_);
        return v___x_6054_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14___boxed(
    mut v_t_6055_: *mut leanh::LeanObject,
    mut v___y_6056_: *mut leanh::LeanObject,
    mut v___y_6057_: *mut leanh::LeanObject,
    mut v___y_6058_: *mut leanh::LeanObject,
    mut v___y_6059_: *mut leanh::LeanObject,
    mut v___y_6060_: *mut leanh::LeanObject,
    mut v___y_6061_: *mut leanh::LeanObject,
    mut v___y_6062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6063_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v_t_6055_, v___y_6056_, v___y_6057_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_);
    leanh::lean_dec(v___y_6061_);
    leanh::lean_dec_ref(v___y_6060_);
    leanh::lean_dec(v___y_6059_);
    leanh::lean_dec_ref(v___y_6058_);
    leanh::lean_dec(v___y_6057_);
    leanh::lean_dec_ref(v___y_6056_);
    return v_res_6063_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(
    mut v_a_6064_: *mut leanh::LeanObject,
    mut v_a_6065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6071_: u8 = 0;
    let mut v___x_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6064_) == 0 {
                    v___x_6066_ = l_List_reverse___redArg(v_a_6065_);
                    return v___x_6066_;
                } else {
                    v_head_6067_ = leanh::lean_ctor_get(v_a_6064_, 0);
                    v_tail_6068_ = leanh::lean_ctor_get(v_a_6064_, 1);
                    v_isSharedCheck_6077_ = (!leanh::lean_is_exclusive(v_a_6064_)) as u8;
                    if v_isSharedCheck_6077_ == 0 {
                        v___x_6070_ = v_a_6064_;
                        v_isShared_6071_ = v_isSharedCheck_6077_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6068_);
                        leanh::lean_inc(v_head_6067_);
                        leanh::lean_dec(v_a_6064_);
                        v___x_6070_ = leanh::lean_box(0);
                        v_isShared_6071_ = v_isSharedCheck_6077_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6072_ = l_Lean_mkLevelParam(v_head_6067_);
                if v_isShared_6071_ == 0 {
                    leanh::lean_ctor_set(v___x_6070_, 1, v_a_6065_);
                    leanh::lean_ctor_set(v___x_6070_, 0, v___x_6072_);
                    v___x_6074_ = v___x_6070_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6076_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6076_, 0, v___x_6072_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6076_, 1, v_a_6065_);
                    v___x_6074_ = v_reuseFailAlloc_6076_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6064_ = v_tail_6068_;
                v_a_6065_ = v___x_6074_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6078_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6078_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6079_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__0);
    v___x_6080_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6080_, 0, v___x_6079_);
    return v___x_6080_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6081_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
    v___x_6082_ = leanh::lean_unsigned_to_nat(0);
    v___x_6083_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_6083_, 0, v___x_6082_);
    leanh::lean_ctor_set(v___x_6083_, 1, v___x_6082_);
    leanh::lean_ctor_set(v___x_6083_, 2, v___x_6082_);
    leanh::lean_ctor_set(v___x_6083_, 3, v___x_6082_);
    leanh::lean_ctor_set(v___x_6083_, 4, v___x_6081_);
    leanh::lean_ctor_set(v___x_6083_, 5, v___x_6081_);
    leanh::lean_ctor_set(v___x_6083_, 6, v___x_6081_);
    leanh::lean_ctor_set(v___x_6083_, 7, v___x_6081_);
    leanh::lean_ctor_set(v___x_6083_, 8, v___x_6081_);
    leanh::lean_ctor_set(v___x_6083_, 9, v___x_6081_);
    return v___x_6083_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6084_ = leanh::lean_box(1);
    v___x_6085_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3_once
        ),
        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__3,
    );
    v___x_6086_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__1);
    v___x_6087_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6087_, 0, v___x_6086_);
    leanh::lean_ctor_set(v___x_6087_, 1, v___x_6085_);
    leanh::lean_ctor_set(v___x_6087_, 2, v___x_6084_);
    return v___x_6087_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6089_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__4;
    v___x_6090_ = l_Lean_stringToMessageData(v___x_6089_);
    return v___x_6090_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6092_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__6;
    v___x_6093_ = l_Lean_stringToMessageData(v___x_6092_);
    return v___x_6093_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6095_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__8;
    v___x_6096_ = l_Lean_stringToMessageData(v___x_6095_);
    return v___x_6096_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6098_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__10;
    v___x_6099_ = l_Lean_stringToMessageData(v___x_6098_);
    return v___x_6099_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6101_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__12;
    v___x_6102_ = l_Lean_stringToMessageData(v___x_6101_);
    return v___x_6102_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_6104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6104_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__14;
    v___x_6105_ = l_Lean_stringToMessageData(v___x_6104_);
    return v___x_6105_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6107_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__16;
    v___x_6108_ = l_Lean_stringToMessageData(v___x_6107_);
    return v___x_6108_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(
    mut v_msg_6109_: *mut leanh::LeanObject,
    mut v_declHint_6110_: *mut leanh::LeanObject,
    mut v___y_6111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: u8 = 0;
    let mut v_isExporting_6116_: u8 = 0;
    let mut v___x_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: u8 = 0;
    let mut v___x_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6138_: u8 = 0;
    let mut v___x_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: u8 = 0;
    let mut v___x_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6170_: u8 = 0;
    let mut v___x_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6113_ = lean_st_ref_get(v___y_6111_);
                v_env_6114_ = leanh::lean_ctor_get(v___x_6113_, 0);
                leanh::lean_inc_ref(v_env_6114_);
                leanh::lean_dec(v___x_6113_);
                v___x_6115_ = l_Lean_Name_isAnonymous(v_declHint_6110_);
                if v___x_6115_ == 0 {
                    v_isExporting_6116_ = leanh::lean_ctor_get_uint8(
                        v_env_6114_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_6116_ == 0 {
                        leanh::lean_dec_ref(v_env_6114_);
                        leanh::lean_dec(v_declHint_6110_);
                        v___x_6117_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6117_, 0, v_msg_6109_);
                        return v___x_6117_;
                    } else {
                        leanh::lean_inc_ref(v_env_6114_);
                        v___x_6118_ = l_Lean_Environment_setExporting(v_env_6114_, v___x_6115_);
                        leanh::lean_inc(v_declHint_6110_);
                        leanh::lean_inc_ref(v___x_6118_);
                        v___x_6119_ = l_Lean_Environment_contains(
                            v___x_6118_,
                            v_declHint_6110_,
                            v_isExporting_6116_,
                        );
                        if v___x_6119_ == 0 {
                            leanh::lean_dec_ref(v___x_6118_);
                            leanh::lean_dec_ref(v_env_6114_);
                            leanh::lean_dec(v_declHint_6110_);
                            v___x_6120_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_6120_, 0, v_msg_6109_);
                            return v___x_6120_;
                        } else {
                            v___x_6121_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__2);
                            v___x_6122_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__3);
                            v___x_6123_ = l_Lean_Options_empty;
                            v___x_6124_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_6124_, 0, v___x_6118_);
                            leanh::lean_ctor_set(v___x_6124_, 1, v___x_6121_);
                            leanh::lean_ctor_set(v___x_6124_, 2, v___x_6122_);
                            leanh::lean_ctor_set(v___x_6124_, 3, v___x_6123_);
                            leanh::lean_inc(v_declHint_6110_);
                            v___x_6125_ =
                                l_Lean_MessageData_ofConstName(v_declHint_6110_, v___x_6115_);
                            v_c_6126_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_6126_, 0, v___x_6124_);
                            leanh::lean_ctor_set(v_c_6126_, 1, v___x_6125_);
                            v___x_6127_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_6114_,
                                v_declHint_6110_,
                            );
                            if leanh::lean_obj_tag(v___x_6127_) == 0 {
                                leanh::lean_dec_ref(v_env_6114_);
                                leanh::lean_dec(v_declHint_6110_);
                                v___x_6128_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
                                v___x_6129_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_6129_, 0, v___x_6128_);
                                leanh::lean_ctor_set(v___x_6129_, 1, v_c_6126_);
                                v___x_6130_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__7);
                                v___x_6131_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_6131_, 0, v___x_6129_);
                                leanh::lean_ctor_set(v___x_6131_, 1, v___x_6130_);
                                v___x_6132_ = l_Lean_MessageData_note(v___x_6131_);
                                v___x_6133_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_6133_, 0, v_msg_6109_);
                                leanh::lean_ctor_set(v___x_6133_, 1, v___x_6132_);
                                v___x_6134_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_6134_, 0, v___x_6133_);
                                return v___x_6134_;
                            } else {
                                v_val_6135_ = leanh::lean_ctor_get(v___x_6127_, 0);
                                v_isSharedCheck_6170_ =
                                    (!leanh::lean_is_exclusive(v___x_6127_)) as u8;
                                if v_isSharedCheck_6170_ == 0 {
                                    v___x_6137_ = v___x_6127_;
                                    v_isShared_6138_ = v_isSharedCheck_6170_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_6135_);
                                    leanh::lean_dec(v___x_6127_);
                                    v___x_6137_ = leanh::lean_box(0);
                                    v_isShared_6138_ = v_isSharedCheck_6170_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_6114_);
                    leanh::lean_dec(v_declHint_6110_);
                    v___x_6171_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6171_, 0, v_msg_6109_);
                    return v___x_6171_;
                }
            }
            1 => {
                v___x_6139_ = leanh::lean_box(0);
                v___x_6140_ = l_Lean_Environment_header(v_env_6114_);
                leanh::lean_dec_ref(v_env_6114_);
                v___x_6141_ = l_Lean_EnvironmentHeader_moduleNames(v___x_6140_);
                v_mod_6142_ = lean_array_get(v___x_6139_, v___x_6141_, v_val_6135_);
                leanh::lean_dec(v_val_6135_);
                leanh::lean_dec_ref(v___x_6141_);
                v___x_6143_ = l_Lean_isPrivateName(v_declHint_6110_);
                leanh::lean_dec(v_declHint_6110_);
                if v___x_6143_ == 0 {
                    v___x_6144_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__9);
                    v___x_6145_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6145_, 0, v___x_6144_);
                    leanh::lean_ctor_set(v___x_6145_, 1, v_c_6126_);
                    v___x_6146_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__11);
                    v___x_6147_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6147_, 0, v___x_6145_);
                    leanh::lean_ctor_set(v___x_6147_, 1, v___x_6146_);
                    v___x_6148_ = l_Lean_MessageData_ofName(v_mod_6142_);
                    v___x_6149_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6149_, 0, v___x_6147_);
                    leanh::lean_ctor_set(v___x_6149_, 1, v___x_6148_);
                    v___x_6150_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__13);
                    v___x_6151_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6151_, 0, v___x_6149_);
                    leanh::lean_ctor_set(v___x_6151_, 1, v___x_6150_);
                    v___x_6152_ = l_Lean_MessageData_note(v___x_6151_);
                    v___x_6153_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6153_, 0, v_msg_6109_);
                    leanh::lean_ctor_set(v___x_6153_, 1, v___x_6152_);
                    if v_isShared_6138_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6137_, 0);
                        leanh::lean_ctor_set(v___x_6137_, 0, v___x_6153_);
                        v___x_6155_ = v___x_6137_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6156_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6156_, 0, v___x_6153_);
                        v___x_6155_ = v_reuseFailAlloc_6156_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6157_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__5);
                    v___x_6158_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6158_, 0, v___x_6157_);
                    leanh::lean_ctor_set(v___x_6158_, 1, v_c_6126_);
                    v___x_6159_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__15);
                    v___x_6160_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6160_, 0, v___x_6158_);
                    leanh::lean_ctor_set(v___x_6160_, 1, v___x_6159_);
                    v___x_6161_ = l_Lean_MessageData_ofName(v_mod_6142_);
                    v___x_6162_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6162_, 0, v___x_6160_);
                    leanh::lean_ctor_set(v___x_6162_, 1, v___x_6161_);
                    v___x_6163_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___closed__17);
                    v___x_6164_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6164_, 0, v___x_6162_);
                    leanh::lean_ctor_set(v___x_6164_, 1, v___x_6163_);
                    v___x_6165_ = l_Lean_MessageData_note(v___x_6164_);
                    v___x_6166_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6166_, 0, v_msg_6109_);
                    leanh::lean_ctor_set(v___x_6166_, 1, v___x_6165_);
                    if v_isShared_6138_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6137_, 0);
                        leanh::lean_ctor_set(v___x_6137_, 0, v___x_6166_);
                        v___x_6168_ = v___x_6137_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6169_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6169_, 0, v___x_6166_);
                        v___x_6168_ = v_reuseFailAlloc_6169_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6155_;
            }
            3 => {
                return v___x_6168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg___boxed(
    mut v_msg_6172_: *mut leanh::LeanObject,
    mut v_declHint_6173_: *mut leanh::LeanObject,
    mut v___y_6174_: *mut leanh::LeanObject,
    mut v___y_6175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6176_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_6172_, v_declHint_6173_, v___y_6174_);
    leanh::lean_dec(v___y_6174_);
    return v_res_6176_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(
    mut v_msg_6177_: *mut leanh::LeanObject,
    mut v_declHint_6178_: *mut leanh::LeanObject,
    mut v___y_6179_: *mut leanh::LeanObject,
    mut v___y_6180_: *mut leanh::LeanObject,
    mut v___y_6181_: *mut leanh::LeanObject,
    mut v___y_6182_: *mut leanh::LeanObject,
    mut v___y_6183_: *mut leanh::LeanObject,
    mut v___y_6184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6190_: u8 = 0;
    let mut v___x_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6196_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6186_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_6177_, v_declHint_6178_, v___y_6184_);
                v_a_6187_ = leanh::lean_ctor_get(v___x_6186_, 0);
                v_isSharedCheck_6196_ = (!leanh::lean_is_exclusive(v___x_6186_)) as u8;
                if v_isSharedCheck_6196_ == 0 {
                    v___x_6189_ = v___x_6186_;
                    v_isShared_6190_ = v_isSharedCheck_6196_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6187_);
                    leanh::lean_dec(v___x_6186_);
                    v___x_6189_ = leanh::lean_box(0);
                    v_isShared_6190_ = v_isSharedCheck_6196_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6191_ = l_Lean_unknownIdentifierMessageTag;
                v___x_6192_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6192_, 0, v___x_6191_);
                leanh::lean_ctor_set(v___x_6192_, 1, v_a_6187_);
                if v_isShared_6190_ == 0 {
                    leanh::lean_ctor_set(v___x_6189_, 0, v___x_6192_);
                    v___x_6194_ = v___x_6189_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6195_, 0, v___x_6192_);
                    v___x_6194_ = v_reuseFailAlloc_6195_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23___boxed(
    mut v_msg_6197_: *mut leanh::LeanObject,
    mut v_declHint_6198_: *mut leanh::LeanObject,
    mut v___y_6199_: *mut leanh::LeanObject,
    mut v___y_6200_: *mut leanh::LeanObject,
    mut v___y_6201_: *mut leanh::LeanObject,
    mut v___y_6202_: *mut leanh::LeanObject,
    mut v___y_6203_: *mut leanh::LeanObject,
    mut v___y_6204_: *mut leanh::LeanObject,
    mut v___y_6205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6206_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_6197_, v_declHint_6198_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_);
    leanh::lean_dec(v___y_6204_);
    leanh::lean_dec_ref(v___y_6203_);
    leanh::lean_dec(v___y_6202_);
    leanh::lean_dec_ref(v___y_6201_);
    leanh::lean_dec(v___y_6200_);
    leanh::lean_dec_ref(v___y_6199_);
    return v_res_6206_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(
    mut v_ref_6207_: *mut leanh::LeanObject,
    mut v_msg_6208_: *mut leanh::LeanObject,
    mut v___y_6209_: *mut leanh::LeanObject,
    mut v___y_6210_: *mut leanh::LeanObject,
    mut v___y_6211_: *mut leanh::LeanObject,
    mut v___y_6212_: *mut leanh::LeanObject,
    mut v___y_6213_: *mut leanh::LeanObject,
    mut v___y_6214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6228_: u8 = 0;
    let mut v_cancelTk_x3f_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6230_: u8 = 0;
    let mut v_inheritedTraceOptions_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_6216_ = leanh::lean_ctor_get(v___y_6213_, 0);
    v_fileMap_6217_ = leanh::lean_ctor_get(v___y_6213_, 1);
    v_options_6218_ = leanh::lean_ctor_get(v___y_6213_, 2);
    v_currRecDepth_6219_ = leanh::lean_ctor_get(v___y_6213_, 3);
    v_maxRecDepth_6220_ = leanh::lean_ctor_get(v___y_6213_, 4);
    v_ref_6221_ = leanh::lean_ctor_get(v___y_6213_, 5);
    v_currNamespace_6222_ = leanh::lean_ctor_get(v___y_6213_, 6);
    v_openDecls_6223_ = leanh::lean_ctor_get(v___y_6213_, 7);
    v_initHeartbeats_6224_ = leanh::lean_ctor_get(v___y_6213_, 8);
    v_maxHeartbeats_6225_ = leanh::lean_ctor_get(v___y_6213_, 9);
    v_quotContext_6226_ = leanh::lean_ctor_get(v___y_6213_, 10);
    v_currMacroScope_6227_ = leanh::lean_ctor_get(v___y_6213_, 11);
    v_diag_6228_ = leanh::lean_ctor_get_uint8(
        v___y_6213_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_6229_ = leanh::lean_ctor_get(v___y_6213_, 12);
    v_suppressElabErrors_6230_ = leanh::lean_ctor_get_uint8(
        v___y_6213_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_6231_ = leanh::lean_ctor_get(v___y_6213_, 13);
    v_ref_6232_ = l_Lean_replaceRef(v_ref_6207_, v_ref_6221_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_6231_);
    leanh::lean_inc(v_cancelTk_x3f_6229_);
    leanh::lean_inc(v_currMacroScope_6227_);
    leanh::lean_inc(v_quotContext_6226_);
    leanh::lean_inc(v_maxHeartbeats_6225_);
    leanh::lean_inc(v_initHeartbeats_6224_);
    leanh::lean_inc(v_openDecls_6223_);
    leanh::lean_inc(v_currNamespace_6222_);
    leanh::lean_inc(v_maxRecDepth_6220_);
    leanh::lean_inc(v_currRecDepth_6219_);
    leanh::lean_inc_ref(v_options_6218_);
    leanh::lean_inc_ref(v_fileMap_6217_);
    leanh::lean_inc_ref(v_fileName_6216_);
    v___x_6233_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_6233_, 0, v_fileName_6216_);
    leanh::lean_ctor_set(v___x_6233_, 1, v_fileMap_6217_);
    leanh::lean_ctor_set(v___x_6233_, 2, v_options_6218_);
    leanh::lean_ctor_set(v___x_6233_, 3, v_currRecDepth_6219_);
    leanh::lean_ctor_set(v___x_6233_, 4, v_maxRecDepth_6220_);
    leanh::lean_ctor_set(v___x_6233_, 5, v_ref_6232_);
    leanh::lean_ctor_set(v___x_6233_, 6, v_currNamespace_6222_);
    leanh::lean_ctor_set(v___x_6233_, 7, v_openDecls_6223_);
    leanh::lean_ctor_set(v___x_6233_, 8, v_initHeartbeats_6224_);
    leanh::lean_ctor_set(v___x_6233_, 9, v_maxHeartbeats_6225_);
    leanh::lean_ctor_set(v___x_6233_, 10, v_quotContext_6226_);
    leanh::lean_ctor_set(v___x_6233_, 11, v_currMacroScope_6227_);
    leanh::lean_ctor_set(v___x_6233_, 12, v_cancelTk_x3f_6229_);
    leanh::lean_ctor_set(v___x_6233_, 13, v_inheritedTraceOptions_6231_);
    leanh::lean_ctor_set_uint8(
        v___x_6233_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_6228_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_6233_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_6230_,
    );
    v___x_6234_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_, v___x_6233_, v___y_6214_);
    leanh::lean_dec_ref_known(v___x_6233_, 14);
    return v___x_6234_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg___boxed(
    mut v_ref_6235_: *mut leanh::LeanObject,
    mut v_msg_6236_: *mut leanh::LeanObject,
    mut v___y_6237_: *mut leanh::LeanObject,
    mut v___y_6238_: *mut leanh::LeanObject,
    mut v___y_6239_: *mut leanh::LeanObject,
    mut v___y_6240_: *mut leanh::LeanObject,
    mut v___y_6241_: *mut leanh::LeanObject,
    mut v___y_6242_: *mut leanh::LeanObject,
    mut v___y_6243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6244_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_6235_, v_msg_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_, v___y_6242_);
    leanh::lean_dec(v___y_6242_);
    leanh::lean_dec_ref(v___y_6241_);
    leanh::lean_dec(v___y_6240_);
    leanh::lean_dec_ref(v___y_6239_);
    leanh::lean_dec(v___y_6238_);
    leanh::lean_dec_ref(v___y_6237_);
    leanh::lean_dec(v_ref_6235_);
    return v_res_6244_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(
    mut v_ref_6245_: *mut leanh::LeanObject,
    mut v_msg_6246_: *mut leanh::LeanObject,
    mut v_declHint_6247_: *mut leanh::LeanObject,
    mut v___y_6248_: *mut leanh::LeanObject,
    mut v___y_6249_: *mut leanh::LeanObject,
    mut v___y_6250_: *mut leanh::LeanObject,
    mut v___y_6251_: *mut leanh::LeanObject,
    mut v___y_6252_: *mut leanh::LeanObject,
    mut v___y_6253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6255_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23(v_msg_6246_, v_declHint_6247_, v___y_6248_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_);
    v_a_6256_ = leanh::lean_ctor_get(v___x_6255_, 0);
    leanh::lean_inc(v_a_6256_);
    leanh::lean_dec_ref(v___x_6255_);
    v___x_6257_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_6245_, v_a_6256_, v___y_6248_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_);
    return v___x_6257_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg___boxed(
    mut v_ref_6258_: *mut leanh::LeanObject,
    mut v_msg_6259_: *mut leanh::LeanObject,
    mut v_declHint_6260_: *mut leanh::LeanObject,
    mut v___y_6261_: *mut leanh::LeanObject,
    mut v___y_6262_: *mut leanh::LeanObject,
    mut v___y_6263_: *mut leanh::LeanObject,
    mut v___y_6264_: *mut leanh::LeanObject,
    mut v___y_6265_: *mut leanh::LeanObject,
    mut v___y_6266_: *mut leanh::LeanObject,
    mut v___y_6267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6268_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_6258_, v_msg_6259_, v_declHint_6260_, v___y_6261_, v___y_6262_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_);
    leanh::lean_dec(v___y_6266_);
    leanh::lean_dec_ref(v___y_6265_);
    leanh::lean_dec(v___y_6264_);
    leanh::lean_dec_ref(v___y_6263_);
    leanh::lean_dec(v___y_6262_);
    leanh::lean_dec_ref(v___y_6261_);
    leanh::lean_dec(v_ref_6258_);
    return v_res_6268_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6270_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__0;
    v___x_6271_ = l_Lean_stringToMessageData(v___x_6270_);
    return v___x_6271_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(
    mut v_ref_6272_: *mut leanh::LeanObject,
    mut v_constName_6273_: *mut leanh::LeanObject,
    mut v___y_6274_: *mut leanh::LeanObject,
    mut v___y_6275_: *mut leanh::LeanObject,
    mut v___y_6276_: *mut leanh::LeanObject,
    mut v___y_6277_: *mut leanh::LeanObject,
    mut v___y_6278_: *mut leanh::LeanObject,
    mut v___y_6279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: u8 = 0;
    let mut v___x_6283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6281_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___closed__1);
    v___x_6282_ = 0;
    leanh::lean_inc(v_constName_6273_);
    v___x_6283_ = l_Lean_MessageData_ofConstName(v_constName_6273_, v___x_6282_);
    v___x_6284_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6284_, 0, v___x_6281_);
    leanh::lean_ctor_set(v___x_6284_, 1, v___x_6283_);
    v___x_6285_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once
        ),
        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1,
    );
    v___x_6286_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6286_, 0, v___x_6284_);
    leanh::lean_ctor_set(v___x_6286_, 1, v___x_6285_);
    v___x_6287_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_6272_, v___x_6286_, v_constName_6273_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_, v___y_6278_, v___y_6279_);
    return v___x_6287_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg___boxed(
    mut v_ref_6288_: *mut leanh::LeanObject,
    mut v_constName_6289_: *mut leanh::LeanObject,
    mut v___y_6290_: *mut leanh::LeanObject,
    mut v___y_6291_: *mut leanh::LeanObject,
    mut v___y_6292_: *mut leanh::LeanObject,
    mut v___y_6293_: *mut leanh::LeanObject,
    mut v___y_6294_: *mut leanh::LeanObject,
    mut v___y_6295_: *mut leanh::LeanObject,
    mut v___y_6296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6297_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_6288_, v_constName_6289_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_, v___y_6294_, v___y_6295_);
    leanh::lean_dec(v___y_6295_);
    leanh::lean_dec_ref(v___y_6294_);
    leanh::lean_dec(v___y_6293_);
    leanh::lean_dec_ref(v___y_6292_);
    leanh::lean_dec(v___y_6291_);
    leanh::lean_dec_ref(v___y_6290_);
    leanh::lean_dec(v_ref_6288_);
    return v_res_6297_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(
    mut v_constName_6298_: *mut leanh::LeanObject,
    mut v___y_6299_: *mut leanh::LeanObject,
    mut v___y_6300_: *mut leanh::LeanObject,
    mut v___y_6301_: *mut leanh::LeanObject,
    mut v___y_6302_: *mut leanh::LeanObject,
    mut v___y_6303_: *mut leanh::LeanObject,
    mut v___y_6304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_6306_ = leanh::lean_ctor_get(v___y_6303_, 5);
    v___x_6307_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_6306_, v_constName_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
    return v___x_6307_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg___boxed(
    mut v_constName_6308_: *mut leanh::LeanObject,
    mut v___y_6309_: *mut leanh::LeanObject,
    mut v___y_6310_: *mut leanh::LeanObject,
    mut v___y_6311_: *mut leanh::LeanObject,
    mut v___y_6312_: *mut leanh::LeanObject,
    mut v___y_6313_: *mut leanh::LeanObject,
    mut v___y_6314_: *mut leanh::LeanObject,
    mut v___y_6315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6316_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_6308_, v___y_6309_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_, v___y_6314_);
    leanh::lean_dec(v___y_6314_);
    leanh::lean_dec_ref(v___y_6313_);
    leanh::lean_dec(v___y_6312_);
    leanh::lean_dec_ref(v___y_6311_);
    leanh::lean_dec(v___y_6310_);
    leanh::lean_dec_ref(v___y_6309_);
    return v_res_6316_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(
    mut v_constName_6317_: *mut leanh::LeanObject,
    mut v___y_6318_: *mut leanh::LeanObject,
    mut v___y_6319_: *mut leanh::LeanObject,
    mut v___y_6320_: *mut leanh::LeanObject,
    mut v___y_6321_: *mut leanh::LeanObject,
    mut v___y_6322_: *mut leanh::LeanObject,
    mut v___y_6323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: u8 = 0;
    let mut v___x_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6333_: u8 = 0;
    let mut v___x_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6325_ = lean_st_ref_get(v___y_6323_);
                v_env_6326_ = leanh::lean_ctor_get(v___x_6325_, 0);
                leanh::lean_inc_ref(v_env_6326_);
                leanh::lean_dec(v___x_6325_);
                v___x_6327_ = 0;
                leanh::lean_inc(v_constName_6317_);
                v___x_6328_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_6326_,
                    v_constName_6317_,
                    v___x_6327_,
                );
                if leanh::lean_obj_tag(v___x_6328_) == 0 {
                    v___x_6329_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_6317_, v___y_6318_, v___y_6319_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_);
                    return v___x_6329_;
                } else {
                    leanh::lean_dec(v_constName_6317_);
                    v_val_6330_ = leanh::lean_ctor_get(v___x_6328_, 0);
                    v_isSharedCheck_6337_ = (!leanh::lean_is_exclusive(v___x_6328_)) as u8;
                    if v_isSharedCheck_6337_ == 0 {
                        v___x_6332_ = v___x_6328_;
                        v_isShared_6333_ = v_isSharedCheck_6337_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6330_);
                        leanh::lean_dec(v___x_6328_);
                        v___x_6332_ = leanh::lean_box(0);
                        v_isShared_6333_ = v_isSharedCheck_6337_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6333_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6332_, 0);
                    v___x_6335_ = v___x_6332_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6336_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6336_, 0, v_val_6330_);
                    v___x_6335_ = v_reuseFailAlloc_6336_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14___boxed(
    mut v_constName_6338_: *mut leanh::LeanObject,
    mut v___y_6339_: *mut leanh::LeanObject,
    mut v___y_6340_: *mut leanh::LeanObject,
    mut v___y_6341_: *mut leanh::LeanObject,
    mut v___y_6342_: *mut leanh::LeanObject,
    mut v___y_6343_: *mut leanh::LeanObject,
    mut v___y_6344_: *mut leanh::LeanObject,
    mut v___y_6345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6346_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_6338_, v___y_6339_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_);
    leanh::lean_dec(v___y_6344_);
    leanh::lean_dec_ref(v___y_6343_);
    leanh::lean_dec(v___y_6342_);
    leanh::lean_dec_ref(v___y_6341_);
    leanh::lean_dec(v___y_6340_);
    leanh::lean_dec_ref(v___y_6339_);
    return v_res_6346_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(
    mut v_constName_6347_: *mut leanh::LeanObject,
    mut v___y_6348_: *mut leanh::LeanObject,
    mut v___y_6349_: *mut leanh::LeanObject,
    mut v___y_6350_: *mut leanh::LeanObject,
    mut v___y_6351_: *mut leanh::LeanObject,
    mut v___y_6352_: *mut leanh::LeanObject,
    mut v___y_6353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6359_: u8 = 0;
    let mut v_levelParams_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6367_: u8 = 0;
    let mut v_a_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6371_: u8 = 0;
    let mut v___x_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_constName_6347_);
                v___x_6355_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14(v_constName_6347_, v___y_6348_, v___y_6349_, v___y_6350_, v___y_6351_, v___y_6352_, v___y_6353_);
                if leanh::lean_obj_tag(v___x_6355_) == 0 {
                    v_a_6356_ = leanh::lean_ctor_get(v___x_6355_, 0);
                    v_isSharedCheck_6367_ = (!leanh::lean_is_exclusive(v___x_6355_)) as u8;
                    if v_isSharedCheck_6367_ == 0 {
                        v___x_6358_ = v___x_6355_;
                        v_isShared_6359_ = v_isSharedCheck_6367_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6356_);
                        leanh::lean_dec(v___x_6355_);
                        v___x_6358_ = leanh::lean_box(0);
                        v_isShared_6359_ = v_isSharedCheck_6367_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_constName_6347_);
                    v_a_6368_ = leanh::lean_ctor_get(v___x_6355_, 0);
                    v_isSharedCheck_6375_ = (!leanh::lean_is_exclusive(v___x_6355_)) as u8;
                    if v_isSharedCheck_6375_ == 0 {
                        v___x_6370_ = v___x_6355_;
                        v_isShared_6371_ = v_isSharedCheck_6375_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6368_);
                        leanh::lean_dec(v___x_6355_);
                        v___x_6370_ = leanh::lean_box(0);
                        v_isShared_6371_ = v_isSharedCheck_6375_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_6360_ = leanh::lean_ctor_get(v_a_6356_, 1);
                leanh::lean_inc(v_levelParams_6360_);
                leanh::lean_dec(v_a_6356_);
                v___x_6361_ = leanh::lean_box(0);
                v___x_6362_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__15(v_levelParams_6360_, v___x_6361_);
                v___x_6363_ = l_Lean_mkConst(v_constName_6347_, v___x_6362_);
                if v_isShared_6359_ == 0 {
                    leanh::lean_ctor_set(v___x_6358_, 0, v___x_6363_);
                    v___x_6365_ = v___x_6358_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6366_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6366_, 0, v___x_6363_);
                    v___x_6365_ = v_reuseFailAlloc_6366_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6365_;
            }
            3 => {
                if v_isShared_6371_ == 0 {
                    v___x_6373_ = v___x_6370_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6374_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6374_, 0, v_a_6368_);
                    v___x_6373_ = v_reuseFailAlloc_6374_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13___boxed(
    mut v_constName_6376_: *mut leanh::LeanObject,
    mut v___y_6377_: *mut leanh::LeanObject,
    mut v___y_6378_: *mut leanh::LeanObject,
    mut v___y_6379_: *mut leanh::LeanObject,
    mut v___y_6380_: *mut leanh::LeanObject,
    mut v___y_6381_: *mut leanh::LeanObject,
    mut v___y_6382_: *mut leanh::LeanObject,
    mut v___y_6383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6384_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_constName_6376_, v___y_6377_, v___y_6378_, v___y_6379_, v___y_6380_, v___y_6381_, v___y_6382_);
    leanh::lean_dec(v___y_6382_);
    leanh::lean_dec_ref(v___y_6381_);
    leanh::lean_dec(v___y_6380_);
    leanh::lean_dec_ref(v___y_6379_);
    leanh::lean_dec(v___y_6378_);
    leanh::lean_dec_ref(v___y_6377_);
    return v_res_6384_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(
    mut v___x_6385_: u8,
    mut v_declName_6386_: *mut leanh::LeanObject,
    mut v___y_6387_: *mut leanh::LeanObject,
    mut v___y_6388_: *mut leanh::LeanObject,
    mut v___y_6389_: *mut leanh::LeanObject,
    mut v___y_6390_: *mut leanh::LeanObject,
    mut v___y_6391_: *mut leanh::LeanObject,
    mut v___y_6392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6409_: u8 = 0;
    let mut v___x_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6394_ = leanh::lean_ctor_get(v___y_6391_, 5);
                v___x_6395_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13(v_declName_6386_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_, v___y_6391_, v___y_6392_);
                if leanh::lean_obj_tag(v___x_6395_) == 0 {
                    v_a_6396_ = leanh::lean_ctor_get(v___x_6395_, 0);
                    leanh::lean_inc(v_a_6396_);
                    leanh::lean_dec_ref_known(v___x_6395_, 1);
                    v___x_6397_ = leanh::lean_box(0);
                    leanh::lean_inc(v_ref_6394_);
                    v___x_6398_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6398_, 0, v___x_6397_);
                    leanh::lean_ctor_set(v___x_6398_, 1, v_ref_6394_);
                    v___x_6399_ = leanh::lean_unsigned_to_nat(32);
                    v___x_6400_ = lean_mk_empty_array_with_capacity(v___x_6399_);
                    leanh::lean_dec_ref(v___x_6400_);
                    v___x_6401_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4_once
                        ),
                        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__0___closed__4,
                    );
                    v___x_6402_ = leanh::lean_box(0);
                    v___x_6403_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
                    leanh::lean_ctor_set(v___x_6403_, 0, v___x_6398_);
                    leanh::lean_ctor_set(v___x_6403_, 1, v___x_6401_);
                    leanh::lean_ctor_set(v___x_6403_, 2, v___x_6402_);
                    leanh::lean_ctor_set(v___x_6403_, 3, v_a_6396_);
                    leanh::lean_ctor_set_uint8(
                        v___x_6403_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v___x_6385_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_6403_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                        v___x_6385_,
                    );
                    v___x_6404_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6404_, 0, v___x_6403_);
                    v___x_6405_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14(v___x_6404_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_, v___y_6391_, v___y_6392_);
                    return v___x_6405_;
                } else {
                    v_a_6406_ = leanh::lean_ctor_get(v___x_6395_, 0);
                    v_isSharedCheck_6413_ = (!leanh::lean_is_exclusive(v___x_6395_)) as u8;
                    if v_isSharedCheck_6413_ == 0 {
                        v___x_6408_ = v___x_6395_;
                        v_isShared_6409_ = v_isSharedCheck_6413_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6406_);
                        leanh::lean_dec(v___x_6395_);
                        v___x_6408_ = leanh::lean_box(0);
                        v_isShared_6409_ = v_isSharedCheck_6413_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6409_ == 0 {
                    v___x_6411_ = v___x_6408_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6412_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6412_, 0, v_a_6406_);
                    v___x_6411_ = v_reuseFailAlloc_6412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0___boxed(
    mut v___x_6414_: *mut leanh::LeanObject,
    mut v_declName_6415_: *mut leanh::LeanObject,
    mut v___y_6416_: *mut leanh::LeanObject,
    mut v___y_6417_: *mut leanh::LeanObject,
    mut v___y_6418_: *mut leanh::LeanObject,
    mut v___y_6419_: *mut leanh::LeanObject,
    mut v___y_6420_: *mut leanh::LeanObject,
    mut v___y_6421_: *mut leanh::LeanObject,
    mut v___y_6422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_18250__boxed_6423_: u8 = 0;
    let mut v_res_6424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_18250__boxed_6423_ = (leanh::lean_unbox(v___x_6414_) as u8);
    v_res_6424_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__0(v___x_18250__boxed_6423_, v_declName_6415_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_, v___y_6420_, v___y_6421_);
    leanh::lean_dec(v___y_6421_);
    leanh::lean_dec_ref(v___y_6420_);
    leanh::lean_dec(v___y_6419_);
    leanh::lean_dec_ref(v___y_6418_);
    leanh::lean_dec(v___y_6417_);
    leanh::lean_dec_ref(v___y_6416_);
    return v_res_6424_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(
    mut v___f_6425_: *mut leanh::LeanObject,
    mut v___y_6426_: *mut leanh::LeanObject,
    mut v___y_6427_: *mut leanh::LeanObject,
    mut v___y_6428_: *mut leanh::LeanObject,
    mut v___y_6429_: *mut leanh::LeanObject,
    mut v___y_6430_: *mut leanh::LeanObject,
    mut v___y_6431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6433_ = lean_st_ref_get(v___y_6431_);
    v_env_6434_ = leanh::lean_ctor_get(v___x_6433_, 0);
    leanh::lean_inc_ref(v_env_6434_);
    leanh::lean_dec(v___x_6433_);
    v___x_6435_ = leanh::lean_apply_8(
        v___f_6425_,
        v_env_6434_,
        v___y_6426_,
        v___y_6427_,
        v___y_6428_,
        v___y_6429_,
        v___y_6430_,
        v___y_6431_,
        leanh::lean_box(0),
    );
    return v___x_6435_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed(
    mut v___f_6436_: *mut leanh::LeanObject,
    mut v___y_6437_: *mut leanh::LeanObject,
    mut v___y_6438_: *mut leanh::LeanObject,
    mut v___y_6439_: *mut leanh::LeanObject,
    mut v___y_6440_: *mut leanh::LeanObject,
    mut v___y_6441_: *mut leanh::LeanObject,
    mut v___y_6442_: *mut leanh::LeanObject,
    mut v___y_6443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6444_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4(v___f_6436_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_);
    return v_res_6444_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6445_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6445_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6446_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__0);
    v___x_6447_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6447_, 0, v___x_6446_);
    return v___x_6447_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6448_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
    v___x_6449_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6449_, 0, v___x_6448_);
    leanh::lean_ctor_set(v___x_6449_, 1, v___x_6448_);
    return v___x_6449_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6450_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__1);
    v___x_6451_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_6451_, 0, v___x_6450_);
    leanh::lean_ctor_set(v___x_6451_, 1, v___x_6450_);
    leanh::lean_ctor_set(v___x_6451_, 2, v___x_6450_);
    leanh::lean_ctor_set(v___x_6451_, 3, v___x_6450_);
    leanh::lean_ctor_set(v___x_6451_, 4, v___x_6450_);
    leanh::lean_ctor_set(v___x_6451_, 5, v___x_6450_);
    return v___x_6451_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(
    mut v_env_6452_: *mut leanh::LeanObject,
    mut v___y_6453_: *mut leanh::LeanObject,
    mut v___y_6454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6466_: u8 = 0;
    let mut v___x_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6478_: u8 = 0;
    let mut v___x_6479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6486_: u8 = 0;
    let mut v_unused_6487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6489_: u8 = 0;
    let mut v_unused_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6456_ = lean_st_ref_take(v___y_6454_);
                v_nextMacroScope_6457_ = leanh::lean_ctor_get(v___x_6456_, 1);
                v_ngen_6458_ = leanh::lean_ctor_get(v___x_6456_, 2);
                v_auxDeclNGen_6459_ = leanh::lean_ctor_get(v___x_6456_, 3);
                v_traceState_6460_ = leanh::lean_ctor_get(v___x_6456_, 4);
                v_messages_6461_ = leanh::lean_ctor_get(v___x_6456_, 6);
                v_infoState_6462_ = leanh::lean_ctor_get(v___x_6456_, 7);
                v_snapshotTasks_6463_ = leanh::lean_ctor_get(v___x_6456_, 8);
                v_isSharedCheck_6489_ = (!leanh::lean_is_exclusive(v___x_6456_)) as u8;
                if v_isSharedCheck_6489_ == 0 {
                    v_unused_6490_ = leanh::lean_ctor_get(v___x_6456_, 5);
                    leanh::lean_dec(v_unused_6490_);
                    v_unused_6491_ = leanh::lean_ctor_get(v___x_6456_, 0);
                    leanh::lean_dec(v_unused_6491_);
                    v___x_6465_ = v___x_6456_;
                    v_isShared_6466_ = v_isSharedCheck_6489_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6463_);
                    leanh::lean_inc(v_infoState_6462_);
                    leanh::lean_inc(v_messages_6461_);
                    leanh::lean_inc(v_traceState_6460_);
                    leanh::lean_inc(v_auxDeclNGen_6459_);
                    leanh::lean_inc(v_ngen_6458_);
                    leanh::lean_inc(v_nextMacroScope_6457_);
                    leanh::lean_dec(v___x_6456_);
                    v___x_6465_ = leanh::lean_box(0);
                    v_isShared_6466_ = v_isSharedCheck_6489_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6467_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
                if v_isShared_6466_ == 0 {
                    leanh::lean_ctor_set(v___x_6465_, 5, v___x_6467_);
                    leanh::lean_ctor_set(v___x_6465_, 0, v_env_6452_);
                    v___x_6469_ = v___x_6465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6488_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6488_, 0, v_env_6452_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6488_, 1, v_nextMacroScope_6457_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6488_, 2, v_ngen_6458_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6488_, 3, v_auxDeclNGen_6459_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6488_, 4, v_traceState_6460_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6488_, 5, v___x_6467_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6488_, 6, v_messages_6461_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6488_, 7, v_infoState_6462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6488_, 8, v_snapshotTasks_6463_);
                    v___x_6469_ = v_reuseFailAlloc_6488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6470_ = lean_st_ref_set(v___y_6454_, v___x_6469_);
                v___x_6471_ = lean_st_ref_take(v___y_6453_);
                v_mctx_6472_ = leanh::lean_ctor_get(v___x_6471_, 0);
                v_zetaDeltaFVarIds_6473_ = leanh::lean_ctor_get(v___x_6471_, 2);
                v_postponed_6474_ = leanh::lean_ctor_get(v___x_6471_, 3);
                v_diag_6475_ = leanh::lean_ctor_get(v___x_6471_, 4);
                v_isSharedCheck_6486_ = (!leanh::lean_is_exclusive(v___x_6471_)) as u8;
                if v_isSharedCheck_6486_ == 0 {
                    v_unused_6487_ = leanh::lean_ctor_get(v___x_6471_, 1);
                    leanh::lean_dec(v_unused_6487_);
                    v___x_6477_ = v___x_6471_;
                    v_isShared_6478_ = v_isSharedCheck_6486_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_6475_);
                    leanh::lean_inc(v_postponed_6474_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_6473_);
                    leanh::lean_inc(v_mctx_6472_);
                    leanh::lean_dec(v___x_6471_);
                    v___x_6477_ = leanh::lean_box(0);
                    v_isShared_6478_ = v_isSharedCheck_6486_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6479_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
                if v_isShared_6478_ == 0 {
                    leanh::lean_ctor_set(v___x_6477_, 1, v___x_6479_);
                    v___x_6481_ = v___x_6477_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6485_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6485_, 0, v_mctx_6472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6485_, 1, v___x_6479_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6485_,
                        2,
                        v_zetaDeltaFVarIds_6473_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6485_, 3, v_postponed_6474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6485_, 4, v_diag_6475_);
                    v___x_6481_ = v_reuseFailAlloc_6485_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6482_ = lean_st_ref_set(v___y_6453_, v___x_6481_);
                v___x_6483_ = leanh::lean_box(0);
                v___x_6484_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6484_, 0, v___x_6483_);
                return v___x_6484_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___boxed(
    mut v_env_6492_: *mut leanh::LeanObject,
    mut v___y_6493_: *mut leanh::LeanObject,
    mut v___y_6494_: *mut leanh::LeanObject,
    mut v___y_6495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6496_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_6492_, v___y_6493_, v___y_6494_);
    leanh::lean_dec(v___y_6494_);
    leanh::lean_dec(v___y_6493_);
    return v_res_6496_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(
    mut v_env_6497_: *mut leanh::LeanObject,
    mut v_x_6498_: *mut leanh::LeanObject,
    mut v___y_6499_: *mut leanh::LeanObject,
    mut v___y_6500_: *mut leanh::LeanObject,
    mut v___y_6501_: *mut leanh::LeanObject,
    mut v___y_6502_: *mut leanh::LeanObject,
    mut v___y_6503_: *mut leanh::LeanObject,
    mut v___y_6504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6513_: u8 = 0;
    let mut v___x_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6517_: u8 = 0;
    let mut v_unused_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6525_: u8 = 0;
    let mut v___x_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6529_: u8 = 0;
    let mut v_unused_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6506_ = lean_st_ref_get(v___y_6504_);
                v_env_6507_ = leanh::lean_ctor_get(v___x_6506_, 0);
                leanh::lean_inc_ref(v_env_6507_);
                leanh::lean_dec(v___x_6506_);
                v___x_6519_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_6497_, v___y_6502_, v___y_6504_);
                leanh::lean_dec_ref(v___x_6519_);
                leanh::lean_inc(v___y_6504_);
                leanh::lean_inc_ref(v___y_6503_);
                leanh::lean_inc(v___y_6502_);
                leanh::lean_inc_ref(v___y_6501_);
                leanh::lean_inc(v___y_6500_);
                leanh::lean_inc_ref(v___y_6499_);
                v___x_6520_ = leanh::lean_apply_7(
                    v_x_6498_,
                    v___y_6499_,
                    v___y_6500_,
                    v___y_6501_,
                    v___y_6502_,
                    v___y_6503_,
                    v___y_6504_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_6520_) == 0 {
                    v_a_6521_ = leanh::lean_ctor_get(v___x_6520_, 0);
                    leanh::lean_inc(v_a_6521_);
                    leanh::lean_dec_ref_known(v___x_6520_, 1);
                    v___x_6522_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_6507_, v___y_6502_, v___y_6504_);
                    v_isSharedCheck_6529_ = (!leanh::lean_is_exclusive(v___x_6522_)) as u8;
                    if v_isSharedCheck_6529_ == 0 {
                        v_unused_6530_ = leanh::lean_ctor_get(v___x_6522_, 0);
                        leanh::lean_dec(v_unused_6530_);
                        v___x_6524_ = v___x_6522_;
                        v_isShared_6525_ = v_isSharedCheck_6529_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6522_);
                        v___x_6524_ = leanh::lean_box(0);
                        v_isShared_6525_ = v_isSharedCheck_6529_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_6531_ = leanh::lean_ctor_get(v___x_6520_, 0);
                    leanh::lean_inc(v_a_6531_);
                    leanh::lean_dec_ref_known(v___x_6520_, 1);
                    v_a_6509_ = v_a_6531_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6510_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_6507_, v___y_6502_, v___y_6504_);
                v_isSharedCheck_6517_ = (!leanh::lean_is_exclusive(v___x_6510_)) as u8;
                if v_isSharedCheck_6517_ == 0 {
                    v_unused_6518_ = leanh::lean_ctor_get(v___x_6510_, 0);
                    leanh::lean_dec(v_unused_6518_);
                    v___x_6512_ = v___x_6510_;
                    v_isShared_6513_ = v_isSharedCheck_6517_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_6510_);
                    v___x_6512_ = leanh::lean_box(0);
                    v_isShared_6513_ = v_isSharedCheck_6517_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6513_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6512_, 1);
                    leanh::lean_ctor_set(v___x_6512_, 0, v_a_6509_);
                    v___x_6515_ = v___x_6512_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6516_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6516_, 0, v_a_6509_);
                    v___x_6515_ = v_reuseFailAlloc_6516_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6515_;
            }
            4 => {
                if v_isShared_6525_ == 0 {
                    leanh::lean_ctor_set(v___x_6524_, 0, v_a_6521_);
                    v___x_6527_ = v___x_6524_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6528_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6528_, 0, v_a_6521_);
                    v___x_6527_ = v_reuseFailAlloc_6528_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg___boxed(
    mut v_env_6532_: *mut leanh::LeanObject,
    mut v_x_6533_: *mut leanh::LeanObject,
    mut v___y_6534_: *mut leanh::LeanObject,
    mut v___y_6535_: *mut leanh::LeanObject,
    mut v___y_6536_: *mut leanh::LeanObject,
    mut v___y_6537_: *mut leanh::LeanObject,
    mut v___y_6538_: *mut leanh::LeanObject,
    mut v___y_6539_: *mut leanh::LeanObject,
    mut v___y_6540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6541_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_6532_, v_x_6533_, v___y_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_);
    leanh::lean_dec(v___y_6539_);
    leanh::lean_dec_ref(v___y_6538_);
    leanh::lean_dec(v___y_6537_);
    leanh::lean_dec_ref(v___y_6536_);
    leanh::lean_dec(v___y_6535_);
    leanh::lean_dec_ref(v___y_6534_);
    return v_res_6541_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(
    mut v_declName_6542_: *mut leanh::LeanObject,
    mut v_env_6543_: *mut leanh::LeanObject,
    mut v_addInfo_6544_: *mut leanh::LeanObject,
    mut v_____r_6545_: *mut leanh::LeanObject,
    mut v___y_6546_: *mut leanh::LeanObject,
    mut v___y_6547_: *mut leanh::LeanObject,
    mut v___y_6548_: *mut leanh::LeanObject,
    mut v___y_6549_: *mut leanh::LeanObject,
    mut v___y_6550_: *mut leanh::LeanObject,
    mut v___y_6551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6559_: u8 = 0;
    let mut v___x_6560_: u8 = 0;
    let mut v___x_6561_: u8 = 0;
    let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6553_ = lean_private_to_user_name(v_declName_6542_);
                if leanh::lean_obj_tag(v___x_6553_) == 0 {
                    leanh::lean_dec_ref(v_addInfo_6544_);
                    leanh::lean_dec_ref(v_env_6543_);
                    v___x_6554_ = leanh::lean_box(0);
                    v___x_6555_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6555_, 0, v___x_6554_);
                    return v___x_6555_;
                } else {
                    v_val_6556_ = leanh::lean_ctor_get(v___x_6553_, 0);
                    v_isSharedCheck_6573_ = (!leanh::lean_is_exclusive(v___x_6553_)) as u8;
                    if v_isSharedCheck_6573_ == 0 {
                        v___x_6558_ = v___x_6553_;
                        v_isShared_6559_ = v_isSharedCheck_6573_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6556_);
                        leanh::lean_dec(v___x_6553_);
                        v___x_6558_ = leanh::lean_box(0);
                        v_isShared_6559_ = v_isSharedCheck_6573_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6560_ = 1;
                leanh::lean_inc(v_val_6556_);
                v___x_6561_ = l_Lean_Environment_contains(v_env_6543_, v_val_6556_, v___x_6560_);
                if v___x_6561_ == 0 {
                    leanh::lean_dec(v_val_6556_);
                    leanh::lean_dec_ref(v_addInfo_6544_);
                    v___x_6562_ = leanh::lean_box(0);
                    if v_isShared_6559_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6558_, 0);
                        leanh::lean_ctor_set(v___x_6558_, 0, v___x_6562_);
                        v___x_6564_ = v___x_6558_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6565_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6565_, 0, v___x_6562_);
                        v___x_6564_ = v_reuseFailAlloc_6565_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6558_);
                    leanh::lean_inc(v___y_6551_);
                    leanh::lean_inc_ref(v___y_6550_);
                    leanh::lean_inc(v___y_6549_);
                    leanh::lean_inc_ref(v___y_6548_);
                    leanh::lean_inc(v___y_6547_);
                    leanh::lean_inc_ref(v___y_6546_);
                    leanh::lean_inc(v_val_6556_);
                    v___x_6566_ = leanh::lean_apply_8(
                        v_addInfo_6544_,
                        v_val_6556_,
                        v___y_6546_,
                        v___y_6547_,
                        v___y_6548_,
                        v___y_6549_,
                        v___y_6550_,
                        v___y_6551_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_6566_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6566_, 1);
                        v___x_6567_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1_once), _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__1);
                        v___x_6568_ = l_Lean_MessageData_ofConstName(v_val_6556_, v___x_6560_);
                        v___x_6569_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6569_, 0, v___x_6567_);
                        leanh::lean_ctor_set(v___x_6569_, 1, v___x_6568_);
                        v___x_6570_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once), _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3);
                        v___x_6571_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6571_, 0, v___x_6569_);
                        leanh::lean_ctor_set(v___x_6571_, 1, v___x_6570_);
                        v___x_6572_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_6571_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_, v___y_6550_, v___y_6551_);
                        return v___x_6572_;
                    } else {
                        leanh::lean_dec(v_val_6556_);
                        return v___x_6566_;
                    }
                }
            }
            2 => {
                return v___x_6564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed(
    mut v_declName_6574_: *mut leanh::LeanObject,
    mut v_env_6575_: *mut leanh::LeanObject,
    mut v_addInfo_6576_: *mut leanh::LeanObject,
    mut v_____r_6577_: *mut leanh::LeanObject,
    mut v___y_6578_: *mut leanh::LeanObject,
    mut v___y_6579_: *mut leanh::LeanObject,
    mut v___y_6580_: *mut leanh::LeanObject,
    mut v___y_6581_: *mut leanh::LeanObject,
    mut v___y_6582_: *mut leanh::LeanObject,
    mut v___y_6583_: *mut leanh::LeanObject,
    mut v___y_6584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6585_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1(v_declName_6574_, v_env_6575_, v_addInfo_6576_, v_____r_6577_, v___y_6578_, v___y_6579_, v___y_6580_, v___y_6581_, v___y_6582_, v___y_6583_);
    leanh::lean_dec(v___y_6583_);
    leanh::lean_dec_ref(v___y_6582_);
    leanh::lean_dec(v___y_6581_);
    leanh::lean_dec_ref(v___y_6580_);
    leanh::lean_dec(v___y_6579_);
    leanh::lean_dec_ref(v___y_6578_);
    return v_res_6585_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(
    mut v_addInfo_6586_: *mut leanh::LeanObject,
    mut v_declName_6587_: *mut leanh::LeanObject,
    mut v___x_6588_: u8,
    mut v___f_6589_: *mut leanh::LeanObject,
    mut v___x_6590_: u8,
    mut v_env_6591_: *mut leanh::LeanObject,
    mut v___f_6592_: *mut leanh::LeanObject,
    mut v___y_6593_: *mut leanh::LeanObject,
    mut v___y_6594_: *mut leanh::LeanObject,
    mut v___y_6595_: *mut leanh::LeanObject,
    mut v___y_6596_: *mut leanh::LeanObject,
    mut v___y_6597_: *mut leanh::LeanObject,
    mut v___y_6598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_6598_);
    leanh::lean_inc_ref(v___y_6597_);
    leanh::lean_inc(v___y_6596_);
    leanh::lean_inc_ref(v___y_6595_);
    leanh::lean_inc(v___y_6594_);
    leanh::lean_inc_ref(v___y_6593_);
    leanh::lean_inc(v_declName_6587_);
    v___x_6600_ = leanh::lean_apply_8(
        v_addInfo_6586_,
        v_declName_6587_,
        v___y_6593_,
        v___y_6594_,
        v___y_6595_,
        v___y_6596_,
        v___y_6597_,
        v___y_6598_,
        leanh::lean_box(0),
    );
    if leanh::lean_obj_tag(v___x_6600_) == 0 {
        let mut v___x_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_6600_, 1);
        leanh::lean_inc(v_declName_6587_);
        v___x_6601_ = lean_private_to_user_name(v_declName_6587_);
        if leanh::lean_obj_tag(v___x_6601_) == 0 {
            let mut v___x_6602_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6603_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6604_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6606_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6607_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6602_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once
                ),
                _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1,
            );
            v___x_6603_ = l_Lean_MessageData_ofConstName(v_declName_6587_, v___x_6588_);
            v___x_6604_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_6604_, 0, v___x_6602_);
            leanh::lean_ctor_set(v___x_6604_, 1, v___x_6603_);
            v___x_6605_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once
                ),
                _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3,
            );
            v___x_6606_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_6606_, 0, v___x_6604_);
            leanh::lean_ctor_set(v___x_6606_, 1, v___x_6605_);
            v___x_6607_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_6606_, v___y_6593_, v___y_6594_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_);
            leanh::lean_dec(v___y_6598_);
            leanh::lean_dec_ref(v___y_6597_);
            leanh::lean_dec(v___y_6596_);
            leanh::lean_dec_ref(v___y_6595_);
            leanh::lean_dec(v___y_6594_);
            leanh::lean_dec_ref(v___y_6593_);
            return v___x_6607_;
        } else {
            let mut v_val_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6609_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6610_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6614_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_declName_6587_);
            v_val_6608_ = leanh::lean_ctor_get(v___x_6601_, 0);
            leanh::lean_inc(v_val_6608_);
            leanh::lean_dec_ref_known(v___x_6601_, 1);
            v___x_6609_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1_once
                ),
                _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__11___closed__1,
            );
            v___x_6610_ = l_Lean_MessageData_ofConstName(v_val_6608_, v___x_6588_);
            v___x_6611_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_6611_, 0, v___x_6609_);
            leanh::lean_ctor_set(v___x_6611_, 1, v___x_6610_);
            v___x_6612_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once
                ),
                _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3,
            );
            v___x_6613_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_6613_, 0, v___x_6611_);
            leanh::lean_ctor_set(v___x_6613_, 1, v___x_6612_);
            v___x_6614_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_6613_, v___y_6593_, v___y_6594_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_);
            leanh::lean_dec(v___y_6598_);
            leanh::lean_dec_ref(v___y_6597_);
            leanh::lean_dec(v___y_6596_);
            leanh::lean_dec_ref(v___y_6595_);
            leanh::lean_dec(v___y_6594_);
            leanh::lean_dec_ref(v___y_6593_);
            return v___x_6614_;
        }
    } else {
        leanh::lean_dec(v___y_6598_);
        leanh::lean_dec_ref(v___y_6597_);
        leanh::lean_dec(v___y_6596_);
        leanh::lean_dec_ref(v___y_6595_);
        leanh::lean_dec(v___y_6594_);
        leanh::lean_dec_ref(v___y_6593_);
        leanh::lean_dec(v_declName_6587_);
        return v___x_6600_;
    }
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed(
    mut v_addInfo_6615_: *mut leanh::LeanObject,
    mut v_declName_6616_: *mut leanh::LeanObject,
    mut v___x_6617_: *mut leanh::LeanObject,
    mut v___f_6618_: *mut leanh::LeanObject,
    mut v___x_6619_: *mut leanh::LeanObject,
    mut v_env_6620_: *mut leanh::LeanObject,
    mut v___f_6621_: *mut leanh::LeanObject,
    mut v___y_6622_: *mut leanh::LeanObject,
    mut v___y_6623_: *mut leanh::LeanObject,
    mut v___y_6624_: *mut leanh::LeanObject,
    mut v___y_6625_: *mut leanh::LeanObject,
    mut v___y_6626_: *mut leanh::LeanObject,
    mut v___y_6627_: *mut leanh::LeanObject,
    mut v___y_6628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_18604__boxed_6629_: u8 = 0;
    let mut v___x_18606__boxed_6630_: u8 = 0;
    let mut v_res_6631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_18604__boxed_6629_ = (leanh::lean_unbox(v___x_6617_) as u8);
    v___x_18606__boxed_6630_ = (leanh::lean_unbox(v___x_6619_) as u8);
    v_res_6631_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5(v_addInfo_6615_, v_declName_6616_, v___x_18604__boxed_6629_, v___f_6618_, v___x_18606__boxed_6630_, v_env_6620_, v___f_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_, v___y_6627_);
    leanh::lean_dec_ref(v___f_6621_);
    leanh::lean_dec_ref(v_env_6620_);
    leanh::lean_dec_ref(v___f_6618_);
    return v_res_6631_;
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(
    mut v_declName_6635_: *mut leanh::LeanObject,
    mut v___y_6636_: *mut leanh::LeanObject,
    mut v___y_6637_: *mut leanh::LeanObject,
    mut v___y_6638_: *mut leanh::LeanObject,
    mut v___y_6639_: *mut leanh::LeanObject,
    mut v___y_6640_: *mut leanh::LeanObject,
    mut v___y_6641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: u8 = 0;
    let mut v_addInfo_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: u8 = 0;
    let mut v___x_6653_: u8 = 0;
    v___x_6643_ = lean_st_ref_get(v___y_6641_);
    v_env_6644_ = leanh::lean_ctor_get(v___x_6643_, 0);
    leanh::lean_inc_ref(v_env_6644_);
    leanh::lean_dec(v___x_6643_);
    v___x_6645_ = 0;
    v_addInfo_6646_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___closed__0;
    v_env_6647_ = l_Lean_Environment_setExporting(v_env_6644_, v___x_6645_);
    leanh::lean_inc_ref_n(v_env_6647_, 4);
    leanh::lean_inc_n(v_declName_6635_, 4);
    v___f_6648_ = leanh::lean_alloc_closure(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__1___boxed as *mut core::ffi::c_void, 11, 3);
    leanh::lean_closure_set(v___f_6648_, 0, v_declName_6635_);
    leanh::lean_closure_set(v___f_6648_, 1, v_env_6647_);
    leanh::lean_closure_set(v___f_6648_, 2, v_addInfo_6646_);
    v___f_6649_ = leanh::lean_alloc_closure(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__2___boxed as *mut core::ffi::c_void, 12, 4);
    leanh::lean_closure_set(v___f_6649_, 0, v_env_6647_);
    leanh::lean_closure_set(v___f_6649_, 1, v_declName_6635_);
    leanh::lean_closure_set(v___f_6649_, 2, v___f_6648_);
    leanh::lean_closure_set(v___f_6649_, 3, v_addInfo_6646_);
    v___x_6650_ = leanh::lean_box((v___x_6645_) as usize);
    leanh::lean_inc_ref(v___f_6649_);
    v___f_6651_ = leanh::lean_alloc_closure(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__3___boxed as *mut core::ffi::c_void, 12, 4);
    leanh::lean_closure_set(v___f_6651_, 0, v___f_6649_);
    leanh::lean_closure_set(v___f_6651_, 1, v_declName_6635_);
    leanh::lean_closure_set(v___f_6651_, 2, v___x_6650_);
    leanh::lean_closure_set(v___f_6651_, 3, v_env_6647_);
    v___x_6652_ = 1;
    v___x_6653_ = l_Lean_Environment_contains(v_env_6647_, v_declName_6635_, v___x_6652_);
    if v___x_6653_ == 0 {
        let mut v___f_6654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___f_6649_);
        leanh::lean_dec(v_declName_6635_);
        v___f_6654_ = leanh::lean_alloc_closure(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__4___boxed as *mut core::ffi::c_void, 8, 1);
        leanh::lean_closure_set(v___f_6654_, 0, v___f_6651_);
        v___x_6655_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_6647_, v___f_6654_, v___y_6636_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_, v___y_6641_);
        return v___x_6655_;
    } else {
        let mut v___x_6656_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6657_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6659_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6656_ = leanh::lean_box((v___x_6652_) as usize);
        v___x_6657_ = leanh::lean_box((v___x_6645_) as usize);
        leanh::lean_inc_ref(v_env_6647_);
        v___f_6658_ = leanh::lean_alloc_closure(l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___lam__5___boxed as *mut core::ffi::c_void, 14, 7);
        leanh::lean_closure_set(v___f_6658_, 0, v_addInfo_6646_);
        leanh::lean_closure_set(v___f_6658_, 1, v_declName_6635_);
        leanh::lean_closure_set(v___f_6658_, 2, v___x_6656_);
        leanh::lean_closure_set(v___f_6658_, 3, v___f_6649_);
        leanh::lean_closure_set(v___f_6658_, 4, v___x_6657_);
        leanh::lean_closure_set(v___f_6658_, 5, v_env_6647_);
        leanh::lean_closure_set(v___f_6658_, 6, v___f_6651_);
        v___x_6659_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_6647_, v___f_6658_, v___y_6636_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_, v___y_6641_);
        return v___x_6659_;
    }
}
pub unsafe fn l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8___boxed(
    mut v_declName_6660_: *mut leanh::LeanObject,
    mut v___y_6661_: *mut leanh::LeanObject,
    mut v___y_6662_: *mut leanh::LeanObject,
    mut v___y_6663_: *mut leanh::LeanObject,
    mut v___y_6664_: *mut leanh::LeanObject,
    mut v___y_6665_: *mut leanh::LeanObject,
    mut v___y_6666_: *mut leanh::LeanObject,
    mut v___y_6667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6668_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_6660_, v___y_6661_, v___y_6662_, v___y_6663_, v___y_6664_, v___y_6665_, v___y_6666_);
    leanh::lean_dec(v___y_6666_);
    leanh::lean_dec_ref(v___y_6665_);
    leanh::lean_dec(v___y_6664_);
    leanh::lean_dec_ref(v___y_6663_);
    leanh::lean_dec(v___y_6662_);
    leanh::lean_dec_ref(v___y_6661_);
    return v_res_6668_;
}
pub unsafe fn l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(
    mut v_modifiers_6669_: *mut leanh::LeanObject,
    mut v_declName_6670_: *mut leanh::LeanObject,
    mut v___y_6671_: *mut leanh::LeanObject,
    mut v___y_6672_: *mut leanh::LeanObject,
    mut v___y_6673_: *mut leanh::LeanObject,
    mut v___y_6674_: *mut leanh::LeanObject,
    mut v___y_6675_: *mut leanh::LeanObject,
    mut v___y_6676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_visibility_6680_: u8 = 0;
    let mut v_isProtected_6681_: u8 = 0;
    let mut v_declName_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6693_: u8 = 0;
    let mut v___x_6695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6708_: u8 = 0;
    let mut v___x_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6721_: u8 = 0;
    let mut v___x_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6730_: u8 = 0;
    let mut v_unused_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6733_: u8 = 0;
    let mut v_unused_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6735_: u8 = 0;
    let mut v_unused_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6740_: u8 = 0;
    let mut v___x_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6744_: u8 = 0;
    let mut v___x_6745_: u8 = 0;
    let mut v___x_6746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6678_ = lean_st_ref_get(v___y_6676_);
                v_env_6679_ = leanh::lean_ctor_get(v___x_6678_, 0);
                leanh::lean_inc_ref(v_env_6679_);
                leanh::lean_dec(v___x_6678_);
                v_visibility_6680_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_6669_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_isProtected_6681_ = leanh::lean_ctor_get_uint8(
                    v_modifiers_6669_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                );
                v___x_6745_ =
                    l_Lean_Elab_Visibility_isInferredPublic(v_env_6679_, v_visibility_6680_);
                leanh::lean_dec_ref(v_env_6679_);
                if v___x_6745_ == 0 {
                    v___x_6746_ = lean_st_ref_get(v___y_6676_);
                    v_env_6747_ = leanh::lean_ctor_get(v___x_6746_, 0);
                    leanh::lean_inc_ref(v_env_6747_);
                    leanh::lean_dec(v___x_6746_);
                    v_declName_6748_ = l_Lean_mkPrivateName(v_env_6747_, v_declName_6670_);
                    leanh::lean_dec_ref(v_env_6747_);
                    v_declName_6683_ = v_declName_6748_;
                    v___y_6684_ = v___y_6671_;
                    v___y_6685_ = v___y_6672_;
                    v___y_6686_ = v___y_6673_;
                    v___y_6687_ = v___y_6674_;
                    v___y_6688_ = v___y_6675_;
                    v___y_6689_ = v___y_6676_;
                    state = 1;
                    continue;
                } else {
                    v_declName_6683_ = v_declName_6670_;
                    v___y_6684_ = v___y_6671_;
                    v___y_6685_ = v___y_6672_;
                    v___y_6686_ = v___y_6673_;
                    v___y_6687_ = v___y_6674_;
                    v___y_6688_ = v___y_6675_;
                    v___y_6689_ = v___y_6676_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_declName_6683_);
                v___x_6690_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8(v_declName_6683_, v___y_6684_, v___y_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_);
                if leanh::lean_obj_tag(v___x_6690_) == 0 {
                    v_isSharedCheck_6735_ = (!leanh::lean_is_exclusive(v___x_6690_)) as u8;
                    if v_isSharedCheck_6735_ == 0 {
                        v_unused_6736_ = leanh::lean_ctor_get(v___x_6690_, 0);
                        leanh::lean_dec(v_unused_6736_);
                        v___x_6692_ = v___x_6690_;
                        v_isShared_6693_ = v_isSharedCheck_6735_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6690_);
                        v___x_6692_ = leanh::lean_box(0);
                        v_isShared_6693_ = v_isSharedCheck_6735_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_6683_);
                    v_a_6737_ = leanh::lean_ctor_get(v___x_6690_, 0);
                    v_isSharedCheck_6744_ = (!leanh::lean_is_exclusive(v___x_6690_)) as u8;
                    if v_isSharedCheck_6744_ == 0 {
                        v___x_6739_ = v___x_6690_;
                        v_isShared_6740_ = v_isSharedCheck_6744_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6737_);
                        leanh::lean_dec(v___x_6690_);
                        v___x_6739_ = leanh::lean_box(0);
                        v_isShared_6740_ = v_isSharedCheck_6744_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if v_isProtected_6681_ == 0 {
                    if v_isShared_6693_ == 0 {
                        leanh::lean_ctor_set(v___x_6692_, 0, v_declName_6683_);
                        v___x_6695_ = v___x_6692_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6696_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6696_, 0, v_declName_6683_);
                        v___x_6695_ = v_reuseFailAlloc_6696_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_6697_ = lean_st_ref_take(v___y_6689_);
                    v_env_6698_ = leanh::lean_ctor_get(v___x_6697_, 0);
                    v_nextMacroScope_6699_ = leanh::lean_ctor_get(v___x_6697_, 1);
                    v_ngen_6700_ = leanh::lean_ctor_get(v___x_6697_, 2);
                    v_auxDeclNGen_6701_ = leanh::lean_ctor_get(v___x_6697_, 3);
                    v_traceState_6702_ = leanh::lean_ctor_get(v___x_6697_, 4);
                    v_messages_6703_ = leanh::lean_ctor_get(v___x_6697_, 6);
                    v_infoState_6704_ = leanh::lean_ctor_get(v___x_6697_, 7);
                    v_snapshotTasks_6705_ = leanh::lean_ctor_get(v___x_6697_, 8);
                    v_isSharedCheck_6733_ = (!leanh::lean_is_exclusive(v___x_6697_)) as u8;
                    if v_isSharedCheck_6733_ == 0 {
                        v_unused_6734_ = leanh::lean_ctor_get(v___x_6697_, 5);
                        leanh::lean_dec(v_unused_6734_);
                        v___x_6707_ = v___x_6697_;
                        v_isShared_6708_ = v_isSharedCheck_6733_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_6705_);
                        leanh::lean_inc(v_infoState_6704_);
                        leanh::lean_inc(v_messages_6703_);
                        leanh::lean_inc(v_traceState_6702_);
                        leanh::lean_inc(v_auxDeclNGen_6701_);
                        leanh::lean_inc(v_ngen_6700_);
                        leanh::lean_inc(v_nextMacroScope_6699_);
                        leanh::lean_inc(v_env_6698_);
                        leanh::lean_dec(v___x_6697_);
                        v___x_6707_ = leanh::lean_box(0);
                        v_isShared_6708_ = v_isSharedCheck_6733_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6695_;
            }
            4 => {
                leanh::lean_inc(v_declName_6683_);
                v___x_6709_ = l_Lean_addProtected(v_env_6698_, v_declName_6683_);
                v___x_6710_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__2);
                if v_isShared_6708_ == 0 {
                    leanh::lean_ctor_set(v___x_6707_, 5, v___x_6710_);
                    leanh::lean_ctor_set(v___x_6707_, 0, v___x_6709_);
                    v___x_6712_ = v___x_6707_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6732_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6732_, 0, v___x_6709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6732_, 1, v_nextMacroScope_6699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6732_, 2, v_ngen_6700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6732_, 3, v_auxDeclNGen_6701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6732_, 4, v_traceState_6702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6732_, 5, v___x_6710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6732_, 6, v_messages_6703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6732_, 7, v_infoState_6704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6732_, 8, v_snapshotTasks_6705_);
                    v___x_6712_ = v_reuseFailAlloc_6732_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6713_ = lean_st_ref_set(v___y_6689_, v___x_6712_);
                v___x_6714_ = lean_st_ref_take(v___y_6687_);
                v_mctx_6715_ = leanh::lean_ctor_get(v___x_6714_, 0);
                v_zetaDeltaFVarIds_6716_ = leanh::lean_ctor_get(v___x_6714_, 2);
                v_postponed_6717_ = leanh::lean_ctor_get(v___x_6714_, 3);
                v_diag_6718_ = leanh::lean_ctor_get(v___x_6714_, 4);
                v_isSharedCheck_6730_ = (!leanh::lean_is_exclusive(v___x_6714_)) as u8;
                if v_isSharedCheck_6730_ == 0 {
                    v_unused_6731_ = leanh::lean_ctor_get(v___x_6714_, 1);
                    leanh::lean_dec(v_unused_6731_);
                    v___x_6720_ = v___x_6714_;
                    v_isShared_6721_ = v_isSharedCheck_6730_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_6718_);
                    leanh::lean_inc(v_postponed_6717_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_6716_);
                    leanh::lean_inc(v_mctx_6715_);
                    leanh::lean_dec(v___x_6714_);
                    v___x_6720_ = leanh::lean_box(0);
                    v_isShared_6721_ = v_isSharedCheck_6730_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6722_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg___closed__3);
                if v_isShared_6721_ == 0 {
                    leanh::lean_ctor_set(v___x_6720_, 1, v___x_6722_);
                    v___x_6724_ = v___x_6720_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6729_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 0, v_mctx_6715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 1, v___x_6722_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6729_,
                        2,
                        v_zetaDeltaFVarIds_6716_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 3, v_postponed_6717_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 4, v_diag_6718_);
                    v___x_6724_ = v_reuseFailAlloc_6729_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_6725_ = lean_st_ref_set(v___y_6687_, v___x_6724_);
                if v_isShared_6693_ == 0 {
                    leanh::lean_ctor_set(v___x_6692_, 0, v_declName_6683_);
                    v___x_6727_ = v___x_6692_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6728_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6728_, 0, v_declName_6683_);
                    v___x_6727_ = v_reuseFailAlloc_6728_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6727_;
            }
            9 => {
                if v_isShared_6740_ == 0 {
                    v___x_6742_ = v___x_6739_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6743_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6743_, 0, v_a_6737_);
                    v___x_6742_ = v_reuseFailAlloc_6743_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6742_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4___boxed(
    mut v_modifiers_6749_: *mut leanh::LeanObject,
    mut v_declName_6750_: *mut leanh::LeanObject,
    mut v___y_6751_: *mut leanh::LeanObject,
    mut v___y_6752_: *mut leanh::LeanObject,
    mut v___y_6753_: *mut leanh::LeanObject,
    mut v___y_6754_: *mut leanh::LeanObject,
    mut v___y_6755_: *mut leanh::LeanObject,
    mut v___y_6756_: *mut leanh::LeanObject,
    mut v___y_6757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6758_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_6749_, v_declName_6750_, v___y_6751_, v___y_6752_, v___y_6753_, v___y_6754_, v___y_6755_, v___y_6756_);
    leanh::lean_dec(v___y_6756_);
    leanh::lean_dec_ref(v___y_6755_);
    leanh::lean_dec(v___y_6754_);
    leanh::lean_dec_ref(v___y_6753_);
    leanh::lean_dec(v___y_6752_);
    leanh::lean_dec_ref(v___y_6751_);
    leanh::lean_dec_ref(v_modifiers_6749_);
    return v_res_6758_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(
    mut v_pre_6759_: *mut leanh::LeanObject,
    mut v_declName_6760_: *mut leanh::LeanObject,
    mut v_as_6761_: *mut leanh::LeanObject,
    mut v_sz_6762_: usize,
    mut v_i_6763_: usize,
    mut v_b_6764_: *mut leanh::LeanObject,
    mut v___y_6765_: *mut leanh::LeanObject,
    mut v___y_6766_: *mut leanh::LeanObject,
    mut v___y_6767_: *mut leanh::LeanObject,
    mut v___y_6768_: *mut leanh::LeanObject,
    mut v___y_6769_: *mut leanh::LeanObject,
    mut v___y_6770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: usize = 0;
    let mut v___x_6775_: usize = 0;
    let mut v___x_6777_: u8 = 0;
    let mut v___x_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: u8 = 0;
    let mut v___x_6783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: u8 = 0;
    let mut v___x_6785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6777_ = lean_usize_dec_lt(v_i_6763_, v_sz_6762_);
                if v___x_6777_ == 0 {
                    leanh::lean_dec(v_declName_6760_);
                    leanh::lean_dec(v_pre_6759_);
                    v___x_6778_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6778_, 0, v_b_6764_);
                    return v___x_6778_;
                } else {
                    v___x_6779_ = leanh::lean_box(0);
                    v_a_6780_ = lean_array_uget_borrowed(v_as_6761_, v_i_6763_);
                    leanh::lean_inc(v_a_6780_);
                    leanh::lean_inc(v_pre_6759_);
                    v___x_6781_ = l_Lean_Name_append(v_pre_6759_, v_a_6780_);
                    v___x_6782_ = lean_name_eq(v___x_6781_, v_declName_6760_);
                    leanh::lean_dec(v___x_6781_);
                    if v___x_6782_ == 0 {
                        v_a_6773_ = v___x_6779_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6783_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once), _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
                        v___x_6784_ = 0;
                        leanh::lean_inc(v_declName_6760_);
                        v___x_6785_ = l_Lean_MessageData_ofConstName(v_declName_6760_, v___x_6784_);
                        v___x_6786_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6786_, 0, v___x_6783_);
                        leanh::lean_ctor_set(v___x_6786_, 1, v___x_6785_);
                        v___x_6787_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3_once), _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__3);
                        v___x_6788_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6788_, 0, v___x_6786_);
                        leanh::lean_ctor_set(v___x_6788_, 1, v___x_6787_);
                        leanh::lean_inc(v_pre_6759_);
                        v___x_6789_ = l_Lean_MessageData_ofName(v_pre_6759_);
                        v___x_6790_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6790_, 0, v___x_6788_);
                        leanh::lean_ctor_set(v___x_6790_, 1, v___x_6789_);
                        v___x_6791_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5_once), _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__5);
                        v___x_6792_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6792_, 0, v___x_6790_);
                        leanh::lean_ctor_set(v___x_6792_, 1, v___x_6791_);
                        leanh::lean_inc(v_a_6780_);
                        v___x_6793_ = l_Lean_MessageData_ofName(v_a_6780_);
                        v___x_6794_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6794_, 0, v___x_6792_);
                        leanh::lean_ctor_set(v___x_6794_, 1, v___x_6793_);
                        v___x_6795_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once), _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
                        v___x_6796_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6796_, 0, v___x_6794_);
                        leanh::lean_ctor_set(v___x_6796_, 1, v___x_6795_);
                        v___x_6797_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_6796_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_, v___y_6769_, v___y_6770_);
                        if leanh::lean_obj_tag(v___x_6797_) == 0 {
                            leanh::lean_dec_ref_known(v___x_6797_, 1);
                            v_a_6773_ = v___x_6779_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_declName_6760_);
                            leanh::lean_dec(v_pre_6759_);
                            return v___x_6797_;
                        }
                    }
                }
            }
            1 => {
                v___x_6774_ = 1usize;
                v___x_6775_ = lean_usize_add(v_i_6763_, v___x_6774_);
                v_i_6763_ = v___x_6775_;
                v_b_6764_ = v_a_6773_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6___boxed(
    mut v_pre_6798_: *mut leanh::LeanObject,
    mut v_declName_6799_: *mut leanh::LeanObject,
    mut v_as_6800_: *mut leanh::LeanObject,
    mut v_sz_6801_: *mut leanh::LeanObject,
    mut v_i_6802_: *mut leanh::LeanObject,
    mut v_b_6803_: *mut leanh::LeanObject,
    mut v___y_6804_: *mut leanh::LeanObject,
    mut v___y_6805_: *mut leanh::LeanObject,
    mut v___y_6806_: *mut leanh::LeanObject,
    mut v___y_6807_: *mut leanh::LeanObject,
    mut v___y_6808_: *mut leanh::LeanObject,
    mut v___y_6809_: *mut leanh::LeanObject,
    mut v___y_6810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6811_: usize = 0;
    let mut v_i_boxed_6812_: usize = 0;
    let mut v_res_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6811_ = leanh::lean_unbox_usize(v_sz_6801_);
    leanh::lean_dec(v_sz_6801_);
    v_i_boxed_6812_ = leanh::lean_unbox_usize(v_i_6802_);
    leanh::lean_dec(v_i_6802_);
    v_res_6813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_6798_, v_declName_6799_, v_as_6800_, v_sz_boxed_6811_, v_i_boxed_6812_, v_b_6803_, v___y_6804_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_, v___y_6809_);
    leanh::lean_dec(v___y_6809_);
    leanh::lean_dec_ref(v___y_6808_);
    leanh::lean_dec(v___y_6807_);
    leanh::lean_dec_ref(v___y_6806_);
    leanh::lean_dec(v___y_6805_);
    leanh::lean_dec_ref(v___y_6804_);
    leanh::lean_dec_ref(v_as_6800_);
    return v_res_6813_;
}
pub unsafe fn l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(
    mut v_declName_6814_: *mut leanh::LeanObject,
    mut v___y_6815_: *mut leanh::LeanObject,
    mut v___y_6816_: *mut leanh::LeanObject,
    mut v___y_6817_: *mut leanh::LeanObject,
    mut v___y_6818_: *mut leanh::LeanObject,
    mut v___y_6819_: *mut leanh::LeanObject,
    mut v___y_6820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pre_6822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: u8 = 0;
    let mut v___x_6826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldNames_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6832_: usize = 0;
    let mut v___x_6833_: usize = 0;
    let mut v___x_6834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6837_: u8 = 0;
    let mut v___x_6839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6841_: u8 = 0;
    let mut v_unused_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_declName_6814_) == 1 {
                    v_pre_6822_ = leanh::lean_ctor_get(v_declName_6814_, 0);
                    leanh::lean_inc_n(v_pre_6822_, 2);
                    v___x_6823_ = lean_st_ref_get(v___y_6820_);
                    v_env_6824_ = leanh::lean_ctor_get(v___x_6823_, 0);
                    leanh::lean_inc_ref(v_env_6824_);
                    leanh::lean_dec(v___x_6823_);
                    v___x_6825_ = l_Lean_isStructure(v_env_6824_, v_pre_6822_);
                    if v___x_6825_ == 0 {
                        leanh::lean_dec_ref_known(v_declName_6814_, 2);
                        leanh::lean_dec(v_pre_6822_);
                        v___x_6826_ = leanh::lean_box(0);
                        v___x_6827_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6827_, 0, v___x_6826_);
                        return v___x_6827_;
                    } else {
                        v___x_6828_ = lean_st_ref_get(v___y_6820_);
                        v_env_6829_ = leanh::lean_ctor_get(v___x_6828_, 0);
                        leanh::lean_inc_ref(v_env_6829_);
                        leanh::lean_dec(v___x_6828_);
                        leanh::lean_inc(v_pre_6822_);
                        v_fieldNames_6830_ = l_Lean_getStructureFieldsFlattened(
                            v_env_6829_,
                            v_pre_6822_,
                            v___x_6825_,
                        );
                        v___x_6831_ = leanh::lean_box(0);
                        v_sz_6832_ = lean_array_size(v_fieldNames_6830_);
                        v___x_6833_ = 0usize;
                        v___x_6834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3_spec__6(v_pre_6822_, v_declName_6814_, v_fieldNames_6830_, v_sz_6832_, v___x_6833_, v___x_6831_, v___y_6815_, v___y_6816_, v___y_6817_, v___y_6818_, v___y_6819_, v___y_6820_);
                        leanh::lean_dec_ref(v_fieldNames_6830_);
                        if leanh::lean_obj_tag(v___x_6834_) == 0 {
                            v_isSharedCheck_6841_ =
                                (!leanh::lean_is_exclusive(v___x_6834_)) as u8;
                            if v_isSharedCheck_6841_ == 0 {
                                v_unused_6842_ = leanh::lean_ctor_get(v___x_6834_, 0);
                                leanh::lean_dec(v_unused_6842_);
                                v___x_6836_ = v___x_6834_;
                                v_isShared_6837_ = v_isSharedCheck_6841_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_6834_);
                                v___x_6836_ = leanh::lean_box(0);
                                v_isShared_6837_ = v_isSharedCheck_6841_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_6834_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_declName_6814_);
                    v___x_6843_ = leanh::lean_box(0);
                    v___x_6844_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6844_, 0, v___x_6843_);
                    return v___x_6844_;
                }
            }
            1 => {
                if v_isShared_6837_ == 0 {
                    leanh::lean_ctor_set(v___x_6836_, 0, v___x_6831_);
                    v___x_6839_ = v___x_6836_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6840_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6840_, 0, v___x_6831_);
                    v___x_6839_ = v_reuseFailAlloc_6840_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3___boxed(
    mut v_declName_6845_: *mut leanh::LeanObject,
    mut v___y_6846_: *mut leanh::LeanObject,
    mut v___y_6847_: *mut leanh::LeanObject,
    mut v___y_6848_: *mut leanh::LeanObject,
    mut v___y_6849_: *mut leanh::LeanObject,
    mut v___y_6850_: *mut leanh::LeanObject,
    mut v___y_6851_: *mut leanh::LeanObject,
    mut v___y_6852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6853_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v_declName_6845_, v___y_6846_, v___y_6847_, v___y_6848_, v___y_6849_, v___y_6850_, v___y_6851_);
    leanh::lean_dec(v___y_6851_);
    leanh::lean_dec_ref(v___y_6850_);
    leanh::lean_dec(v___y_6849_);
    leanh::lean_dec_ref(v___y_6848_);
    leanh::lean_dec(v___y_6847_);
    leanh::lean_dec_ref(v___y_6846_);
    return v_res_6853_;
}
pub unsafe fn l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(
    mut v_currNamespace_6854_: *mut leanh::LeanObject,
    mut v_modifiers_6855_: *mut leanh::LeanObject,
    mut v_shortName_6856_: *mut leanh::LeanObject,
    mut v___y_6857_: *mut leanh::LeanObject,
    mut v___y_6858_: *mut leanh::LeanObject,
    mut v___y_6859_: *mut leanh::LeanObject,
    mut v___y_6860_: *mut leanh::LeanObject,
    mut v___y_6861_: *mut leanh::LeanObject,
    mut v___y_6862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shortName_6871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isProtected_6881_: u8 = 0;
    let mut v_a_6882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6885_: u8 = 0;
    let mut v___x_6886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6890_: u8 = 0;
    let mut v_a_6891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6894_: u8 = 0;
    let mut v_str_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6903_: u8 = 0;
    let mut v_a_6904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6905_: u8 = 0;
    let mut v___x_6906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6911_: u8 = 0;
    let mut v___x_6913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6915_: u8 = 0;
    let mut v_a_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6919_: u8 = 0;
    let mut v___x_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6923_: u8 = 0;
    let mut v_a_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6927_: u8 = 0;
    let mut v___x_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6931_: u8 = 0;
    let mut v_view_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_6934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6939_: u8 = 0;
    let mut v___x_6940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRootName_6941_: u8 = 0;
    let mut v___y_6943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shortName_6953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6964_: u8 = 0;
    let mut v___x_6966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6968_: u8 = 0;
    let mut v___y_6970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: u8 = 0;
    let mut v___x_6984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6989_: u8 = 0;
    let mut v___x_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6993_: u8 = 0;
    let mut v_isSharedCheck_6994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_shortName_6856_);
                v_view_6932_ = l_Lean_extractMacroScopes(v_shortName_6856_);
                v_name_6933_ = leanh::lean_ctor_get(v_view_6932_, 0);
                v_imported_6934_ = leanh::lean_ctor_get(v_view_6932_, 1);
                v_ctx_6935_ = leanh::lean_ctor_get(v_view_6932_, 2);
                v_scopes_6936_ = leanh::lean_ctor_get(v_view_6932_, 3);
                v_isSharedCheck_6994_ = (!leanh::lean_is_exclusive(v_view_6932_)) as u8;
                if v_isSharedCheck_6994_ == 0 {
                    v___x_6938_ = v_view_6932_;
                    v_isShared_6939_ = v_isSharedCheck_6994_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc(v_scopes_6936_);
                    leanh::lean_inc(v_ctx_6935_);
                    leanh::lean_inc(v_imported_6934_);
                    leanh::lean_inc(v_name_6933_);
                    leanh::lean_dec(v_view_6932_);
                    v___x_6938_ = leanh::lean_box(0);
                    v_isShared_6939_ = v_isSharedCheck_6994_;
                    state = 13;
                    continue;
                }
            }
            1 => {
                v___x_6867_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6867_, 0, v___y_6865_);
                leanh::lean_ctor_set(v___x_6867_, 1, v___y_6866_);
                v___x_6868_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6868_, 0, v___x_6867_);
                return v___x_6868_;
            }
            2 => {
                leanh::lean_inc(v___y_6870_);
                v___x_6879_ = l_Lean_Elab_checkIfShadowingStructureField___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__3(v___y_6870_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_, v___y_6877_, v___y_6878_);
                if leanh::lean_obj_tag(v___x_6879_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6879_, 1);
                    v___x_6880_ = l_Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4(v_modifiers_6855_, v___y_6870_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_, v___y_6877_, v___y_6878_);
                    if leanh::lean_obj_tag(v___x_6880_) == 0 {
                        v_isProtected_6881_ = leanh::lean_ctor_get_uint8(
                            v_modifiers_6855_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                        );
                        if v_isProtected_6881_ == 0 {
                            leanh::lean_dec(v_currNamespace_6872_);
                            v_a_6882_ = leanh::lean_ctor_get(v___x_6880_, 0);
                            v_isSharedCheck_6890_ =
                                (!leanh::lean_is_exclusive(v___x_6880_)) as u8;
                            if v_isSharedCheck_6890_ == 0 {
                                v___x_6884_ = v___x_6880_;
                                v_isShared_6885_ = v_isSharedCheck_6890_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6882_);
                                leanh::lean_dec(v___x_6880_);
                                v___x_6884_ = leanh::lean_box(0);
                                v_isShared_6885_ = v_isSharedCheck_6890_;
                                state = 3;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v_currNamespace_6872_) == 1 {
                                v_a_6891_ = leanh::lean_ctor_get(v___x_6880_, 0);
                                v_isSharedCheck_6903_ =
                                    (!leanh::lean_is_exclusive(v___x_6880_)) as u8;
                                if v_isSharedCheck_6903_ == 0 {
                                    v___x_6893_ = v___x_6880_;
                                    v_isShared_6894_ = v_isSharedCheck_6903_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6891_);
                                    leanh::lean_dec(v___x_6880_);
                                    v___x_6893_ = leanh::lean_box(0);
                                    v_isShared_6894_ = v_isSharedCheck_6903_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_currNamespace_6872_);
                                v_a_6904_ = leanh::lean_ctor_get(v___x_6880_, 0);
                                leanh::lean_inc(v_a_6904_);
                                leanh::lean_dec_ref_known(v___x_6880_, 1);
                                v___x_6905_ = l_Lean_Name_isAtomic(v_shortName_6871_);
                                if v___x_6905_ == 0 {
                                    v___y_6865_ = v_a_6904_;
                                    v___y_6866_ = v_shortName_6871_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_6904_);
                                    leanh::lean_dec(v_shortName_6871_);
                                    v___x_6906_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1_once), _init_l_Lean_Elab_mkDeclName___redArg___lam__2___closed__1);
                                    v___x_6907_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_6906_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_, v___y_6877_, v___y_6878_);
                                    v_a_6908_ = leanh::lean_ctor_get(v___x_6907_, 0);
                                    v_isSharedCheck_6915_ =
                                        (!leanh::lean_is_exclusive(v___x_6907_)) as u8;
                                    if v_isSharedCheck_6915_ == 0 {
                                        v___x_6910_ = v___x_6907_;
                                        v_isShared_6911_ = v_isSharedCheck_6915_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6908_);
                                        leanh::lean_dec(v___x_6907_);
                                        v___x_6910_ = leanh::lean_box(0);
                                        v_isShared_6911_ = v_isSharedCheck_6915_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_currNamespace_6872_);
                        leanh::lean_dec(v_shortName_6871_);
                        v_a_6916_ = leanh::lean_ctor_get(v___x_6880_, 0);
                        v_isSharedCheck_6923_ =
                            (!leanh::lean_is_exclusive(v___x_6880_)) as u8;
                        if v_isSharedCheck_6923_ == 0 {
                            v___x_6918_ = v___x_6880_;
                            v_isShared_6919_ = v_isSharedCheck_6923_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6916_);
                            leanh::lean_dec(v___x_6880_);
                            v___x_6918_ = leanh::lean_box(0);
                            v_isShared_6919_ = v_isSharedCheck_6923_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_currNamespace_6872_);
                    leanh::lean_dec(v_shortName_6871_);
                    leanh::lean_dec(v___y_6870_);
                    v_a_6924_ = leanh::lean_ctor_get(v___x_6879_, 0);
                    v_isSharedCheck_6931_ = (!leanh::lean_is_exclusive(v___x_6879_)) as u8;
                    if v_isSharedCheck_6931_ == 0 {
                        v___x_6926_ = v___x_6879_;
                        v_isShared_6927_ = v_isSharedCheck_6931_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6924_);
                        leanh::lean_dec(v___x_6879_);
                        v___x_6926_ = leanh::lean_box(0);
                        v_isShared_6927_ = v_isSharedCheck_6931_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6886_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6886_, 0, v_a_6882_);
                leanh::lean_ctor_set(v___x_6886_, 1, v_shortName_6871_);
                if v_isShared_6885_ == 0 {
                    leanh::lean_ctor_set(v___x_6884_, 0, v___x_6886_);
                    v___x_6888_ = v___x_6884_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6889_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6889_, 0, v___x_6886_);
                    v___x_6888_ = v_reuseFailAlloc_6889_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6888_;
            }
            5 => {
                v_str_6895_ = leanh::lean_ctor_get(v_currNamespace_6872_, 1);
                leanh::lean_inc_ref(v_str_6895_);
                leanh::lean_dec_ref_known(v_currNamespace_6872_, 2);
                v___x_6896_ = leanh::lean_box(0);
                v___x_6897_ = l_Lean_Name_str___override(v___x_6896_, v_str_6895_);
                v___x_6898_ = l_Lean_Name_append(v___x_6897_, v_shortName_6871_);
                v___x_6899_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6899_, 0, v_a_6891_);
                leanh::lean_ctor_set(v___x_6899_, 1, v___x_6898_);
                if v_isShared_6894_ == 0 {
                    leanh::lean_ctor_set(v___x_6893_, 0, v___x_6899_);
                    v___x_6901_ = v___x_6893_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6902_, 0, v___x_6899_);
                    v___x_6901_ = v_reuseFailAlloc_6902_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6901_;
            }
            7 => {
                if v_isShared_6911_ == 0 {
                    v___x_6913_ = v___x_6910_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6914_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6914_, 0, v_a_6908_);
                    v___x_6913_ = v_reuseFailAlloc_6914_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6913_;
            }
            9 => {
                if v_isShared_6919_ == 0 {
                    v___x_6921_ = v___x_6918_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6922_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6922_, 0, v_a_6916_);
                    v___x_6921_ = v_reuseFailAlloc_6922_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6921_;
            }
            11 => {
                if v_isShared_6927_ == 0 {
                    v___x_6929_ = v___x_6926_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6930_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6930_, 0, v_a_6924_);
                    v___x_6929_ = v_reuseFailAlloc_6930_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6929_;
            }
            13 => {
                v___x_6940_ = l_Lean_Elab_mkDeclName___redArg___closed__1;
                v_isRootName_6941_ = l_Lean_Name_isPrefixOf(v___x_6940_, v_name_6933_);
                v___x_6983_ = lean_name_eq(v_name_6933_, v___x_6940_);
                if v___x_6983_ == 0 {
                    v___y_6970_ = v___y_6857_;
                    v___y_6971_ = v___y_6858_;
                    v___y_6972_ = v___y_6859_;
                    v___y_6973_ = v___y_6860_;
                    v___y_6974_ = v___y_6861_;
                    v___y_6975_ = v___y_6862_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_6938_);
                    leanh::lean_dec(v_scopes_6936_);
                    leanh::lean_dec(v_ctx_6935_);
                    leanh::lean_dec(v_imported_6934_);
                    leanh::lean_dec(v_name_6933_);
                    leanh::lean_dec(v_shortName_6856_);
                    leanh::lean_dec(v_currNamespace_6854_);
                    v___x_6984_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_mkDeclName___redArg___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Elab_mkDeclName___redArg___closed__3_once),
                        _init_l_Lean_Elab_mkDeclName___redArg___closed__3,
                    );
                    v___x_6985_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_6984_, v___y_6857_, v___y_6858_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_);
                    v_a_6986_ = leanh::lean_ctor_get(v___x_6985_, 0);
                    v_isSharedCheck_6993_ = (!leanh::lean_is_exclusive(v___x_6985_)) as u8;
                    if v_isSharedCheck_6993_ == 0 {
                        v___x_6988_ = v___x_6985_;
                        v_isShared_6989_ = v_isSharedCheck_6993_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6986_);
                        leanh::lean_dec(v___x_6985_);
                        v___x_6988_ = leanh::lean_box(0);
                        v_isShared_6989_ = v_isSharedCheck_6993_;
                        state = 19;
                        continue;
                    }
                }
            }
            14 => {
                if v_isRootName_6941_ == 0 {
                    leanh::lean_dec(v_name_6933_);
                    v___y_6870_ = v___y_6949_;
                    v_shortName_6871_ = v_shortName_6856_;
                    v_currNamespace_6872_ = v_currNamespace_6854_;
                    v___y_6873_ = v___y_6944_;
                    v___y_6874_ = v___y_6945_;
                    v___y_6875_ = v___y_6947_;
                    v___y_6876_ = v___y_6948_;
                    v___y_6877_ = v___y_6946_;
                    v___y_6878_ = v___y_6943_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_shortName_6856_);
                    leanh::lean_dec(v_currNamespace_6854_);
                    if leanh::lean_obj_tag(v_name_6933_) == 1 {
                        v_pre_6950_ = leanh::lean_ctor_get(v_name_6933_, 0);
                        leanh::lean_inc(v_pre_6950_);
                        v_str_6951_ = leanh::lean_ctor_get(v_name_6933_, 1);
                        leanh::lean_inc_ref(v_str_6951_);
                        leanh::lean_dec_ref_known(v_name_6933_, 2);
                        v___x_6952_ = leanh::lean_box(0);
                        v_shortName_6953_ = l_Lean_Name_str___override(v___x_6952_, v_str_6951_);
                        v_currNamespace_6954_ =
                            l_Lean_Name_replacePrefix(v_pre_6950_, v___x_6940_, v___x_6952_);
                        v___y_6870_ = v___y_6949_;
                        v_shortName_6871_ = v_shortName_6953_;
                        v_currNamespace_6872_ = v_currNamespace_6954_;
                        v___y_6873_ = v___y_6944_;
                        v___y_6874_ = v___y_6945_;
                        v___y_6875_ = v___y_6947_;
                        v___y_6876_ = v___y_6948_;
                        v___y_6877_ = v___y_6946_;
                        v___y_6878_ = v___y_6943_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_6949_);
                        v___x_6955_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1_once), _init_l_Lean_Elab_checkIfShadowingStructureField___redArg___lam__2___closed__1);
                        v___x_6956_ = l_Lean_MessageData_ofName(v_name_6933_);
                        v___x_6957_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6957_, 0, v___x_6955_);
                        leanh::lean_ctor_set(v___x_6957_, 1, v___x_6956_);
                        v___x_6958_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1_once), _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__9___closed__1);
                        v___x_6959_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6959_, 0, v___x_6957_);
                        leanh::lean_ctor_set(v___x_6959_, 1, v___x_6958_);
                        v___x_6960_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_6959_, v___y_6944_, v___y_6945_, v___y_6947_, v___y_6948_, v___y_6946_, v___y_6943_);
                        v_a_6961_ = leanh::lean_ctor_get(v___x_6960_, 0);
                        v_isSharedCheck_6968_ =
                            (!leanh::lean_is_exclusive(v___x_6960_)) as u8;
                        if v_isSharedCheck_6968_ == 0 {
                            v___x_6963_ = v___x_6960_;
                            v_isShared_6964_ = v_isSharedCheck_6968_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6961_);
                            leanh::lean_dec(v___x_6960_);
                            v___x_6963_ = leanh::lean_box(0);
                            v_isShared_6964_ = v_isSharedCheck_6968_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            15 => {
                if v_isShared_6964_ == 0 {
                    v___x_6966_ = v___x_6963_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6967_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6967_, 0, v_a_6961_);
                    v___x_6966_ = v_reuseFailAlloc_6967_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6966_;
            }
            17 => {
                if v_isRootName_6941_ == 0 {
                    leanh::lean_del_object(v___x_6938_);
                    leanh::lean_dec(v_scopes_6936_);
                    leanh::lean_dec(v_ctx_6935_);
                    leanh::lean_dec(v_imported_6934_);
                    leanh::lean_inc(v_shortName_6856_);
                    leanh::lean_inc(v_currNamespace_6854_);
                    v___x_6976_ = l_Lean_Name_append(v_currNamespace_6854_, v_shortName_6856_);
                    v___y_6943_ = v___y_6975_;
                    v___y_6944_ = v___y_6970_;
                    v___y_6945_ = v___y_6971_;
                    v___y_6946_ = v___y_6974_;
                    v___y_6947_ = v___y_6972_;
                    v___y_6948_ = v___y_6973_;
                    v___y_6949_ = v___x_6976_;
                    state = 14;
                    continue;
                } else {
                    v___x_6977_ = leanh::lean_box(0);
                    leanh::lean_inc(v_name_6933_);
                    v___x_6978_ = l_Lean_Name_replacePrefix(v_name_6933_, v___x_6940_, v___x_6977_);
                    if v_isShared_6939_ == 0 {
                        leanh::lean_ctor_set(v___x_6938_, 0, v___x_6978_);
                        v___x_6980_ = v___x_6938_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_6982_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6982_, 0, v___x_6978_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6982_, 1, v_imported_6934_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6982_, 2, v_ctx_6935_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6982_, 3, v_scopes_6936_);
                        v___x_6980_ = v_reuseFailAlloc_6982_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                v___x_6981_ = l_Lean_MacroScopesView_review(v___x_6980_);
                v___y_6943_ = v___y_6975_;
                v___y_6944_ = v___y_6970_;
                v___y_6945_ = v___y_6971_;
                v___y_6946_ = v___y_6974_;
                v___y_6947_ = v___y_6972_;
                v___y_6948_ = v___y_6973_;
                v___y_6949_ = v___x_6981_;
                state = 14;
                continue;
            }
            19 => {
                if v_isShared_6989_ == 0 {
                    v___x_6991_ = v___x_6988_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6992_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6992_, 0, v_a_6986_);
                    v___x_6991_ = v_reuseFailAlloc_6992_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2___boxed(
    mut v_currNamespace_6995_: *mut leanh::LeanObject,
    mut v_modifiers_6996_: *mut leanh::LeanObject,
    mut v_shortName_6997_: *mut leanh::LeanObject,
    mut v___y_6998_: *mut leanh::LeanObject,
    mut v___y_6999_: *mut leanh::LeanObject,
    mut v___y_7000_: *mut leanh::LeanObject,
    mut v___y_7001_: *mut leanh::LeanObject,
    mut v___y_7002_: *mut leanh::LeanObject,
    mut v___y_7003_: *mut leanh::LeanObject,
    mut v___y_7004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7005_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(
        v_currNamespace_6995_,
        v_modifiers_6996_,
        v_shortName_6997_,
        v___y_6998_,
        v___y_6999_,
        v___y_7000_,
        v___y_7001_,
        v___y_7002_,
        v___y_7003_,
    );
    leanh::lean_dec(v___y_7003_);
    leanh::lean_dec_ref(v___y_7002_);
    leanh::lean_dec(v___y_7001_);
    leanh::lean_dec_ref(v___y_7000_);
    leanh::lean_dec(v___y_6999_);
    leanh::lean_dec_ref(v___y_6998_);
    leanh::lean_dec_ref(v_modifiers_6996_);
    return v_res_7005_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(
    mut v___x_7006_: u8,
    mut v_as_7007_: *mut leanh::LeanObject,
    mut v_i_7008_: usize,
    mut v_stop_7009_: usize,
    mut v_b_7010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_7012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: usize = 0;
    let mut v___x_7014_: usize = 0;
    let mut v___x_7016_: u8 = 0;
    let mut v_fst_7017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: u8 = 0;
    let mut v_snd_7019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7022_: u8 = 0;
    let mut v___x_7023_: u8 = 0;
    let mut v___x_7024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7028_: u8 = 0;
    let mut v_unused_7029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7033_: u8 = 0;
    let mut v___x_7034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7040_: u8 = 0;
    let mut v_unused_7041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7016_ = lean_usize_dec_eq(v_i_7008_, v_stop_7009_);
                if v___x_7016_ == 0 {
                    v_fst_7017_ = leanh::lean_ctor_get(v_b_7010_, 0);
                    v___x_7018_ = (leanh::lean_unbox(v_fst_7017_) as u8);
                    if v___x_7018_ == 0 {
                        v_snd_7019_ = leanh::lean_ctor_get(v_b_7010_, 1);
                        v_isSharedCheck_7028_ = (!leanh::lean_is_exclusive(v_b_7010_)) as u8;
                        if v_isSharedCheck_7028_ == 0 {
                            v_unused_7029_ = leanh::lean_ctor_get(v_b_7010_, 0);
                            leanh::lean_dec(v_unused_7029_);
                            v___x_7021_ = v_b_7010_;
                            v_isShared_7022_ = v_isSharedCheck_7028_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_7019_);
                            leanh::lean_dec(v_b_7010_);
                            v___x_7021_ = leanh::lean_box(0);
                            v_isShared_7022_ = v_isSharedCheck_7028_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_7030_ = leanh::lean_ctor_get(v_b_7010_, 1);
                        v_isSharedCheck_7040_ = (!leanh::lean_is_exclusive(v_b_7010_)) as u8;
                        if v_isSharedCheck_7040_ == 0 {
                            v_unused_7041_ = leanh::lean_ctor_get(v_b_7010_, 0);
                            leanh::lean_dec(v_unused_7041_);
                            v___x_7032_ = v_b_7010_;
                            v_isShared_7033_ = v_isSharedCheck_7040_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_7030_);
                            leanh::lean_dec(v_b_7010_);
                            v___x_7032_ = leanh::lean_box(0);
                            v_isShared_7033_ = v_isSharedCheck_7040_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_7010_;
                }
            }
            1 => {
                v___x_7013_ = 1usize;
                v___x_7014_ = lean_usize_add(v_i_7008_, v___x_7013_);
                v_i_7008_ = v___x_7014_;
                v_b_7010_ = v___y_7012_;
                state = 0;
                continue;
            }
            2 => {
                v___x_7023_ = 1;
                v___x_7024_ = leanh::lean_box((v___x_7023_) as usize);
                if v_isShared_7022_ == 0 {
                    leanh::lean_ctor_set(v___x_7021_, 0, v___x_7024_);
                    v___x_7026_ = v___x_7021_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7027_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7027_, 0, v___x_7024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7027_, 1, v_snd_7019_);
                    v___x_7026_ = v_reuseFailAlloc_7027_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_7012_ = v___x_7026_;
                state = 1;
                continue;
            }
            4 => {
                v___x_7034_ = lean_array_uget_borrowed(v_as_7007_, v_i_7008_);
                leanh::lean_inc(v___x_7034_);
                v___x_7035_ = lean_array_push(v_snd_7030_, v___x_7034_);
                v___x_7036_ = leanh::lean_box((v___x_7006_) as usize);
                if v_isShared_7033_ == 0 {
                    leanh::lean_ctor_set(v___x_7032_, 1, v___x_7035_);
                    leanh::lean_ctor_set(v___x_7032_, 0, v___x_7036_);
                    v___x_7038_ = v___x_7032_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7039_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7039_, 0, v___x_7036_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7039_, 1, v___x_7035_);
                    v___x_7038_ = v_reuseFailAlloc_7039_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_7012_ = v___x_7038_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4___boxed(
    mut v___x_7042_: *mut leanh::LeanObject,
    mut v_as_7043_: *mut leanh::LeanObject,
    mut v_i_7044_: *mut leanh::LeanObject,
    mut v_stop_7045_: *mut leanh::LeanObject,
    mut v_b_7046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_19313__boxed_7047_: u8 = 0;
    let mut v_i_boxed_7048_: usize = 0;
    let mut v_stop_boxed_7049_: usize = 0;
    let mut v_res_7050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_19313__boxed_7047_ = (leanh::lean_unbox(v___x_7042_) as u8);
    v_i_boxed_7048_ = leanh::lean_unbox_usize(v_i_7044_);
    leanh::lean_dec(v_i_7044_);
    v_stop_boxed_7049_ = leanh::lean_unbox_usize(v_stop_7045_);
    leanh::lean_dec(v_stop_7045_);
    v_res_7050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_19313__boxed_7047_, v_as_7043_, v_i_boxed_7048_, v_stop_boxed_7049_, v_b_7046_);
    leanh::lean_dec_ref(v_as_7043_);
    return v_res_7050_;
}
pub unsafe fn l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(
    mut v_a_7051_: *mut leanh::LeanObject,
    mut v_x_7052_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7053_: u8 = 0;
    let mut v_head_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7052_) == 0 {
                    v___x_7053_ = 0;
                    return v___x_7053_;
                } else {
                    v_head_7054_ = leanh::lean_ctor_get(v_x_7052_, 0);
                    v_tail_7055_ = leanh::lean_ctor_get(v_x_7052_, 1);
                    v___x_7056_ = lean_name_eq(v_a_7051_, v_head_7054_);
                    if v___x_7056_ == 0 {
                        v_x_7052_ = v_tail_7055_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_7056_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Elab_expandDeclId_spec__0___boxed(
    mut v_a_7058_: *mut leanh::LeanObject,
    mut v_x_7059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7060_: u8 = 0;
    let mut v_r_7061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7060_ = l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_a_7058_, v_x_7059_);
    leanh::lean_dec(v_x_7059_);
    leanh::lean_dec(v_a_7058_);
    v_r_7061_ = leanh::lean_box((v_res_7060_) as usize);
    return v_r_7061_;
}
pub unsafe fn _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7063_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__0;
    v___x_7064_ = l_Lean_stringToMessageData(v___x_7063_);
    return v___x_7064_;
}
pub unsafe fn l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(
    mut v_u_7065_: *mut leanh::LeanObject,
    mut v___y_7066_: *mut leanh::LeanObject,
    mut v___y_7067_: *mut leanh::LeanObject,
    mut v___y_7068_: *mut leanh::LeanObject,
    mut v___y_7069_: *mut leanh::LeanObject,
    mut v___y_7070_: *mut leanh::LeanObject,
    mut v___y_7071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7073_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1_once), _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___closed__1);
    v___x_7074_ = l_Lean_MessageData_ofName(v_u_7065_);
    v___x_7075_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7075_, 0, v___x_7073_);
    leanh::lean_ctor_set(v___x_7075_, 1, v___x_7074_);
    v___x_7076_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3_once
        ),
        _init_l_Lean_Elab_checkNotAlreadyDeclared___redArg___lam__3___closed__3,
    );
    v___x_7077_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7077_, 0, v___x_7075_);
    leanh::lean_ctor_set(v___x_7077_, 1, v___x_7076_);
    v___x_7078_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v___x_7077_, v___y_7066_, v___y_7067_, v___y_7068_, v___y_7069_, v___y_7070_, v___y_7071_);
    return v___x_7078_;
}
pub unsafe fn l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg___boxed(
    mut v_u_7079_: *mut leanh::LeanObject,
    mut v___y_7080_: *mut leanh::LeanObject,
    mut v___y_7081_: *mut leanh::LeanObject,
    mut v___y_7082_: *mut leanh::LeanObject,
    mut v___y_7083_: *mut leanh::LeanObject,
    mut v___y_7084_: *mut leanh::LeanObject,
    mut v___y_7085_: *mut leanh::LeanObject,
    mut v___y_7086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7087_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_7079_, v___y_7080_, v___y_7081_, v___y_7082_, v___y_7083_, v___y_7084_, v___y_7085_);
    leanh::lean_dec(v___y_7085_);
    leanh::lean_dec_ref(v___y_7084_);
    leanh::lean_dec(v___y_7083_);
    leanh::lean_dec_ref(v___y_7082_);
    leanh::lean_dec(v___y_7081_);
    leanh::lean_dec_ref(v___y_7080_);
    return v_res_7087_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(
    mut v_as_7088_: *mut leanh::LeanObject,
    mut v_i_7089_: usize,
    mut v_stop_7090_: usize,
    mut v_b_7091_: *mut leanh::LeanObject,
    mut v___y_7092_: *mut leanh::LeanObject,
    mut v___y_7093_: *mut leanh::LeanObject,
    mut v___y_7094_: *mut leanh::LeanObject,
    mut v___y_7095_: *mut leanh::LeanObject,
    mut v___y_7096_: *mut leanh::LeanObject,
    mut v___y_7097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_7100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: usize = 0;
    let mut v___x_7102_: usize = 0;
    let mut v___x_7104_: u8 = 0;
    let mut v___x_7105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_7106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: u8 = 0;
    let mut v___x_7108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_7109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7121_: u8 = 0;
    let mut v_cancelTk_x3f_7122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7123_: u8 = 0;
    let mut v_inheritedTraceOptions_7124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7104_ = lean_usize_dec_eq(v_i_7089_, v_stop_7090_);
                if v___x_7104_ == 0 {
                    v___x_7105_ = lean_array_uget_borrowed(v_as_7088_, v_i_7089_);
                    v_id_7106_ = l_Lean_Syntax_getId(v___x_7105_);
                    v___x_7107_ =
                        l_List_elem___at___00Lean_Elab_expandDeclId_spec__0(v_id_7106_, v_b_7091_);
                    if v___x_7107_ == 0 {
                        v___x_7108_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7108_, 0, v_id_7106_);
                        leanh::lean_ctor_set(v___x_7108_, 1, v_b_7091_);
                        v_a_7100_ = v___x_7108_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_b_7091_);
                        v_fileName_7109_ = leanh::lean_ctor_get(v___y_7096_, 0);
                        v_fileMap_7110_ = leanh::lean_ctor_get(v___y_7096_, 1);
                        v_options_7111_ = leanh::lean_ctor_get(v___y_7096_, 2);
                        v_currRecDepth_7112_ = leanh::lean_ctor_get(v___y_7096_, 3);
                        v_maxRecDepth_7113_ = leanh::lean_ctor_get(v___y_7096_, 4);
                        v_ref_7114_ = leanh::lean_ctor_get(v___y_7096_, 5);
                        v_currNamespace_7115_ = leanh::lean_ctor_get(v___y_7096_, 6);
                        v_openDecls_7116_ = leanh::lean_ctor_get(v___y_7096_, 7);
                        v_initHeartbeats_7117_ = leanh::lean_ctor_get(v___y_7096_, 8);
                        v_maxHeartbeats_7118_ = leanh::lean_ctor_get(v___y_7096_, 9);
                        v_quotContext_7119_ = leanh::lean_ctor_get(v___y_7096_, 10);
                        v_currMacroScope_7120_ = leanh::lean_ctor_get(v___y_7096_, 11);
                        v_diag_7121_ = leanh::lean_ctor_get_uint8(
                            v___y_7096_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                        );
                        v_cancelTk_x3f_7122_ = leanh::lean_ctor_get(v___y_7096_, 12);
                        v_suppressElabErrors_7123_ = leanh::lean_ctor_get_uint8(
                            v___y_7096_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        );
                        v_inheritedTraceOptions_7124_ =
                            leanh::lean_ctor_get(v___y_7096_, 13);
                        v_ref_7125_ = l_Lean_replaceRef(v___x_7105_, v_ref_7114_);
                        leanh::lean_inc_ref(v_inheritedTraceOptions_7124_);
                        leanh::lean_inc(v_cancelTk_x3f_7122_);
                        leanh::lean_inc(v_currMacroScope_7120_);
                        leanh::lean_inc(v_quotContext_7119_);
                        leanh::lean_inc(v_maxHeartbeats_7118_);
                        leanh::lean_inc(v_initHeartbeats_7117_);
                        leanh::lean_inc(v_openDecls_7116_);
                        leanh::lean_inc(v_currNamespace_7115_);
                        leanh::lean_inc(v_maxRecDepth_7113_);
                        leanh::lean_inc(v_currRecDepth_7112_);
                        leanh::lean_inc_ref(v_options_7111_);
                        leanh::lean_inc_ref(v_fileMap_7110_);
                        leanh::lean_inc_ref(v_fileName_7109_);
                        v___x_7126_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                        leanh::lean_ctor_set(v___x_7126_, 0, v_fileName_7109_);
                        leanh::lean_ctor_set(v___x_7126_, 1, v_fileMap_7110_);
                        leanh::lean_ctor_set(v___x_7126_, 2, v_options_7111_);
                        leanh::lean_ctor_set(v___x_7126_, 3, v_currRecDepth_7112_);
                        leanh::lean_ctor_set(v___x_7126_, 4, v_maxRecDepth_7113_);
                        leanh::lean_ctor_set(v___x_7126_, 5, v_ref_7125_);
                        leanh::lean_ctor_set(v___x_7126_, 6, v_currNamespace_7115_);
                        leanh::lean_ctor_set(v___x_7126_, 7, v_openDecls_7116_);
                        leanh::lean_ctor_set(v___x_7126_, 8, v_initHeartbeats_7117_);
                        leanh::lean_ctor_set(v___x_7126_, 9, v_maxHeartbeats_7118_);
                        leanh::lean_ctor_set(v___x_7126_, 10, v_quotContext_7119_);
                        leanh::lean_ctor_set(v___x_7126_, 11, v_currMacroScope_7120_);
                        leanh::lean_ctor_set(v___x_7126_, 12, v_cancelTk_x3f_7122_);
                        leanh::lean_ctor_set(v___x_7126_, 13, v_inheritedTraceOptions_7124_);
                        leanh::lean_ctor_set_uint8(
                            v___x_7126_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                            v_diag_7121_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_7126_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                            v_suppressElabErrors_7123_,
                        );
                        v___x_7127_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_id_7106_, v___y_7092_, v___y_7093_, v___y_7094_, v___y_7095_, v___x_7126_, v___y_7097_);
                        leanh::lean_dec_ref_known(v___x_7126_, 14);
                        if leanh::lean_obj_tag(v___x_7127_) == 0 {
                            v_a_7128_ = leanh::lean_ctor_get(v___x_7127_, 0);
                            leanh::lean_inc(v_a_7128_);
                            leanh::lean_dec_ref_known(v___x_7127_, 1);
                            v_a_7100_ = v_a_7128_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_7127_;
                        }
                    }
                } else {
                    v___x_7129_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7129_, 0, v_b_7091_);
                    return v___x_7129_;
                }
            }
            1 => {
                v___x_7101_ = 1usize;
                v___x_7102_ = lean_usize_add(v_i_7089_, v___x_7101_);
                v_i_7089_ = v___x_7102_;
                v_b_7091_ = v_a_7100_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3___boxed(
    mut v_as_7130_: *mut leanh::LeanObject,
    mut v_i_7131_: *mut leanh::LeanObject,
    mut v_stop_7132_: *mut leanh::LeanObject,
    mut v_b_7133_: *mut leanh::LeanObject,
    mut v___y_7134_: *mut leanh::LeanObject,
    mut v___y_7135_: *mut leanh::LeanObject,
    mut v___y_7136_: *mut leanh::LeanObject,
    mut v___y_7137_: *mut leanh::LeanObject,
    mut v___y_7138_: *mut leanh::LeanObject,
    mut v___y_7139_: *mut leanh::LeanObject,
    mut v___y_7140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_7141_: usize = 0;
    let mut v_stop_boxed_7142_: usize = 0;
    let mut v_res_7143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7141_ = leanh::lean_unbox_usize(v_i_7131_);
    leanh::lean_dec(v_i_7131_);
    v_stop_boxed_7142_ = leanh::lean_unbox_usize(v_stop_7132_);
    leanh::lean_dec(v_stop_7132_);
    v_res_7143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v_as_7130_, v_i_boxed_7141_, v_stop_boxed_7142_, v_b_7133_, v___y_7134_, v___y_7135_, v___y_7136_, v___y_7137_, v___y_7138_, v___y_7139_);
    leanh::lean_dec(v___y_7139_);
    leanh::lean_dec_ref(v___y_7138_);
    leanh::lean_dec(v___y_7137_);
    leanh::lean_dec_ref(v___y_7136_);
    leanh::lean_dec(v___y_7135_);
    leanh::lean_dec_ref(v___y_7134_);
    leanh::lean_dec_ref(v_as_7130_);
    return v_res_7143_;
}
pub unsafe fn l_Lean_Elab_expandDeclId(
    mut v_currNamespace_7144_: *mut leanh::LeanObject,
    mut v_currLevelNames_7145_: *mut leanh::LeanObject,
    mut v_declId_7146_: *mut leanh::LeanObject,
    mut v_modifiers_7147_: *mut leanh::LeanObject,
    mut v_a_7148_: *mut leanh::LeanObject,
    mut v_a_7149_: *mut leanh::LeanObject,
    mut v_a_7150_: *mut leanh::LeanObject,
    mut v_a_7151_: *mut leanh::LeanObject,
    mut v_a_7152_: *mut leanh::LeanObject,
    mut v_a_7153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7160_: u8 = 0;
    let mut v_levelNames_7162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_7169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7181_: u8 = 0;
    let mut v_cancelTk_x3f_7182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7183_: u8 = 0;
    let mut v_inheritedTraceOptions_7184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7191_: u8 = 0;
    let mut v_fst_7192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_7194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7199_: u8 = 0;
    let mut v_a_7200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7203_: u8 = 0;
    let mut v___x_7205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7207_: u8 = 0;
    let mut v___y_7209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7214_: u8 = 0;
    let mut v___x_7216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7218_: u8 = 0;
    let mut v___y_7220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: u8 = 0;
    let mut v___x_7224_: u8 = 0;
    let mut v___x_7225_: usize = 0;
    let mut v___x_7226_: usize = 0;
    let mut v___x_7227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7228_: usize = 0;
    let mut v___x_7229_: usize = 0;
    let mut v___x_7230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: u8 = 0;
    let mut v___x_7232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: u8 = 0;
    let mut v___x_7239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: u8 = 0;
    let mut v___x_7243_: usize = 0;
    let mut v___x_7244_: usize = 0;
    let mut v___x_7245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: usize = 0;
    let mut v___x_7248_: usize = 0;
    let mut v___x_7249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7155_ = l_Lean_Elab_expandDeclIdCore(v_declId_7146_);
                v_fst_7156_ = leanh::lean_ctor_get(v___x_7155_, 0);
                v_snd_7157_ = leanh::lean_ctor_get(v___x_7155_, 1);
                v_isSharedCheck_7252_ = (!leanh::lean_is_exclusive(v___x_7155_)) as u8;
                if v_isSharedCheck_7252_ == 0 {
                    v___x_7159_ = v___x_7155_;
                    v_isShared_7160_ = v_isSharedCheck_7252_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7157_);
                    leanh::lean_inc(v_fst_7156_);
                    leanh::lean_dec(v___x_7155_);
                    v___x_7159_ = leanh::lean_box(0);
                    v_isShared_7160_ = v_isSharedCheck_7252_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7231_ = l_Lean_Syntax_isNone(v_snd_7157_);
                if v___x_7231_ == 0 {
                    v___x_7232_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7233_ = l_Lean_Syntax_getArg(v_snd_7157_, v___x_7232_);
                    leanh::lean_dec(v_snd_7157_);
                    v___x_7234_ = l_Lean_Syntax_getArgs(v___x_7233_);
                    leanh::lean_dec(v___x_7233_);
                    v___x_7235_ = leanh::lean_unsigned_to_nat(0);
                    v___x_7236_ = l_Lean_Elab_expandDeclIdCore___closed__0;
                    v___x_7237_ = lean_array_get_size(v___x_7234_);
                    v___x_7238_ = lean_nat_dec_lt(v___x_7235_, v___x_7237_);
                    if v___x_7238_ == 0 {
                        leanh::lean_dec_ref(v___x_7234_);
                        leanh::lean_del_object(v___x_7159_);
                        v___y_7220_ = v___x_7236_;
                        state = 10;
                        continue;
                    } else {
                        v___x_7239_ = leanh::lean_box((v___x_7238_) as usize);
                        if v_isShared_7160_ == 0 {
                            leanh::lean_ctor_set(v___x_7159_, 1, v___x_7236_);
                            leanh::lean_ctor_set(v___x_7159_, 0, v___x_7239_);
                            v___x_7241_ = v___x_7159_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_7251_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 0, v___x_7239_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 1, v___x_7236_);
                            v___x_7241_ = v_reuseFailAlloc_7251_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7159_);
                    leanh::lean_dec(v_snd_7157_);
                    v_levelNames_7162_ = v_currLevelNames_7145_;
                    v___y_7163_ = v_a_7148_;
                    v___y_7164_ = v_a_7149_;
                    v___y_7165_ = v_a_7150_;
                    v___y_7166_ = v_a_7151_;
                    v___y_7167_ = v_a_7152_;
                    v___y_7168_ = v_a_7153_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fileName_7169_ = leanh::lean_ctor_get(v___y_7167_, 0);
                v_fileMap_7170_ = leanh::lean_ctor_get(v___y_7167_, 1);
                v_options_7171_ = leanh::lean_ctor_get(v___y_7167_, 2);
                v_currRecDepth_7172_ = leanh::lean_ctor_get(v___y_7167_, 3);
                v_maxRecDepth_7173_ = leanh::lean_ctor_get(v___y_7167_, 4);
                v_ref_7174_ = leanh::lean_ctor_get(v___y_7167_, 5);
                v_currNamespace_7175_ = leanh::lean_ctor_get(v___y_7167_, 6);
                v_openDecls_7176_ = leanh::lean_ctor_get(v___y_7167_, 7);
                v_initHeartbeats_7177_ = leanh::lean_ctor_get(v___y_7167_, 8);
                v_maxHeartbeats_7178_ = leanh::lean_ctor_get(v___y_7167_, 9);
                v_quotContext_7179_ = leanh::lean_ctor_get(v___y_7167_, 10);
                v_currMacroScope_7180_ = leanh::lean_ctor_get(v___y_7167_, 11);
                v_diag_7181_ = leanh::lean_ctor_get_uint8(
                    v___y_7167_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7182_ = leanh::lean_ctor_get(v___y_7167_, 12);
                v_suppressElabErrors_7183_ = leanh::lean_ctor_get_uint8(
                    v___y_7167_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7184_ = leanh::lean_ctor_get(v___y_7167_, 13);
                v_ref_7185_ = l_Lean_replaceRef(v_declId_7146_, v_ref_7174_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_7184_);
                leanh::lean_inc(v_cancelTk_x3f_7182_);
                leanh::lean_inc(v_currMacroScope_7180_);
                leanh::lean_inc(v_quotContext_7179_);
                leanh::lean_inc(v_maxHeartbeats_7178_);
                leanh::lean_inc(v_initHeartbeats_7177_);
                leanh::lean_inc(v_openDecls_7176_);
                leanh::lean_inc(v_currNamespace_7175_);
                leanh::lean_inc(v_maxRecDepth_7173_);
                leanh::lean_inc(v_currRecDepth_7172_);
                leanh::lean_inc_ref(v_options_7171_);
                leanh::lean_inc_ref(v_fileMap_7170_);
                leanh::lean_inc_ref(v_fileName_7169_);
                v___x_7186_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_7186_, 0, v_fileName_7169_);
                leanh::lean_ctor_set(v___x_7186_, 1, v_fileMap_7170_);
                leanh::lean_ctor_set(v___x_7186_, 2, v_options_7171_);
                leanh::lean_ctor_set(v___x_7186_, 3, v_currRecDepth_7172_);
                leanh::lean_ctor_set(v___x_7186_, 4, v_maxRecDepth_7173_);
                leanh::lean_ctor_set(v___x_7186_, 5, v_ref_7185_);
                leanh::lean_ctor_set(v___x_7186_, 6, v_currNamespace_7175_);
                leanh::lean_ctor_set(v___x_7186_, 7, v_openDecls_7176_);
                leanh::lean_ctor_set(v___x_7186_, 8, v_initHeartbeats_7177_);
                leanh::lean_ctor_set(v___x_7186_, 9, v_maxHeartbeats_7178_);
                leanh::lean_ctor_set(v___x_7186_, 10, v_quotContext_7179_);
                leanh::lean_ctor_set(v___x_7186_, 11, v_currMacroScope_7180_);
                leanh::lean_ctor_set(v___x_7186_, 12, v_cancelTk_x3f_7182_);
                leanh::lean_ctor_set(v___x_7186_, 13, v_inheritedTraceOptions_7184_);
                leanh::lean_ctor_set_uint8(
                    v___x_7186_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_7181_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_7186_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7183_,
                );
                v___x_7187_ = l_Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2(
                    v_currNamespace_7144_,
                    v_modifiers_7147_,
                    v_fst_7156_,
                    v___y_7163_,
                    v___y_7164_,
                    v___y_7165_,
                    v___y_7166_,
                    v___x_7186_,
                    v___y_7168_,
                );
                leanh::lean_dec_ref_known(v___x_7186_, 14);
                if leanh::lean_obj_tag(v___x_7187_) == 0 {
                    v_a_7188_ = leanh::lean_ctor_get(v___x_7187_, 0);
                    v_isSharedCheck_7199_ = (!leanh::lean_is_exclusive(v___x_7187_)) as u8;
                    if v_isSharedCheck_7199_ == 0 {
                        v___x_7190_ = v___x_7187_;
                        v_isShared_7191_ = v_isSharedCheck_7199_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7188_);
                        leanh::lean_dec(v___x_7187_);
                        v___x_7190_ = leanh::lean_box(0);
                        v_isShared_7191_ = v_isSharedCheck_7199_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_levelNames_7162_);
                    v_a_7200_ = leanh::lean_ctor_get(v___x_7187_, 0);
                    v_isSharedCheck_7207_ = (!leanh::lean_is_exclusive(v___x_7187_)) as u8;
                    if v_isSharedCheck_7207_ == 0 {
                        v___x_7202_ = v___x_7187_;
                        v_isShared_7203_ = v_isSharedCheck_7207_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7200_);
                        leanh::lean_dec(v___x_7187_);
                        v___x_7202_ = leanh::lean_box(0);
                        v_isShared_7203_ = v_isSharedCheck_7207_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_7192_ = leanh::lean_ctor_get(v_a_7188_, 0);
                leanh::lean_inc(v_fst_7192_);
                v_snd_7193_ = leanh::lean_ctor_get(v_a_7188_, 1);
                leanh::lean_inc(v_snd_7193_);
                leanh::lean_dec(v_a_7188_);
                v_docString_x3f_7194_ = leanh::lean_ctor_get(v_modifiers_7147_, 1);
                leanh::lean_inc(v_docString_x3f_7194_);
                v___x_7195_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_7195_, 0, v_snd_7193_);
                leanh::lean_ctor_set(v___x_7195_, 1, v_fst_7192_);
                leanh::lean_ctor_set(v___x_7195_, 2, v_levelNames_7162_);
                leanh::lean_ctor_set(v___x_7195_, 3, v_docString_x3f_7194_);
                if v_isShared_7191_ == 0 {
                    leanh::lean_ctor_set(v___x_7190_, 0, v___x_7195_);
                    v___x_7197_ = v___x_7190_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7198_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7198_, 0, v___x_7195_);
                    v___x_7197_ = v_reuseFailAlloc_7198_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7197_;
            }
            5 => {
                if v_isShared_7203_ == 0 {
                    v___x_7205_ = v___x_7202_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7206_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7206_, 0, v_a_7200_);
                    v___x_7205_ = v_reuseFailAlloc_7206_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7205_;
            }
            7 => {
                if leanh::lean_obj_tag(v___y_7209_) == 0 {
                    v_a_7210_ = leanh::lean_ctor_get(v___y_7209_, 0);
                    leanh::lean_inc(v_a_7210_);
                    leanh::lean_dec_ref_known(v___y_7209_, 1);
                    v_levelNames_7162_ = v_a_7210_;
                    v___y_7163_ = v_a_7148_;
                    v___y_7164_ = v_a_7149_;
                    v___y_7165_ = v_a_7150_;
                    v___y_7166_ = v_a_7151_;
                    v___y_7167_ = v_a_7152_;
                    v___y_7168_ = v_a_7153_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_7156_);
                    leanh::lean_dec(v_currNamespace_7144_);
                    v_a_7211_ = leanh::lean_ctor_get(v___y_7209_, 0);
                    v_isSharedCheck_7218_ = (!leanh::lean_is_exclusive(v___y_7209_)) as u8;
                    if v_isSharedCheck_7218_ == 0 {
                        v___x_7213_ = v___y_7209_;
                        v_isShared_7214_ = v_isSharedCheck_7218_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7211_);
                        leanh::lean_dec(v___y_7209_);
                        v___x_7213_ = leanh::lean_box(0);
                        v_isShared_7214_ = v_isSharedCheck_7218_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_7214_ == 0 {
                    v___x_7216_ = v___x_7213_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7217_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7217_, 0, v_a_7211_);
                    v___x_7216_ = v_reuseFailAlloc_7217_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7216_;
            }
            10 => {
                v___x_7221_ = leanh::lean_unsigned_to_nat(0);
                v___x_7222_ = lean_array_get_size(v___y_7220_);
                v___x_7223_ = lean_nat_dec_lt(v___x_7221_, v___x_7222_);
                if v___x_7223_ == 0 {
                    leanh::lean_dec_ref(v___y_7220_);
                    v_levelNames_7162_ = v_currLevelNames_7145_;
                    v___y_7163_ = v_a_7148_;
                    v___y_7164_ = v_a_7149_;
                    v___y_7165_ = v_a_7150_;
                    v___y_7166_ = v_a_7151_;
                    v___y_7167_ = v_a_7152_;
                    v___y_7168_ = v_a_7153_;
                    state = 2;
                    continue;
                } else {
                    v___x_7224_ = lean_nat_dec_le(v___x_7222_, v___x_7222_);
                    if v___x_7224_ == 0 {
                        if v___x_7223_ == 0 {
                            leanh::lean_dec_ref(v___y_7220_);
                            v_levelNames_7162_ = v_currLevelNames_7145_;
                            v___y_7163_ = v_a_7148_;
                            v___y_7164_ = v_a_7149_;
                            v___y_7165_ = v_a_7150_;
                            v___y_7166_ = v_a_7151_;
                            v___y_7167_ = v_a_7152_;
                            v___y_7168_ = v_a_7153_;
                            state = 2;
                            continue;
                        } else {
                            v___x_7225_ = 0usize;
                            v___x_7226_ = lean_usize_of_nat(v___x_7222_);
                            v___x_7227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_7220_, v___x_7225_, v___x_7226_, v_currLevelNames_7145_, v_a_7148_, v_a_7149_, v_a_7150_, v_a_7151_, v_a_7152_, v_a_7153_);
                            leanh::lean_dec_ref(v___y_7220_);
                            v___y_7209_ = v___x_7227_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___x_7228_ = 0usize;
                        v___x_7229_ = lean_usize_of_nat(v___x_7222_);
                        v___x_7230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__3(v___y_7220_, v___x_7228_, v___x_7229_, v_currLevelNames_7145_, v_a_7148_, v_a_7149_, v_a_7150_, v_a_7151_, v_a_7152_, v_a_7153_);
                        leanh::lean_dec_ref(v___y_7220_);
                        v___y_7209_ = v___x_7230_;
                        state = 7;
                        continue;
                    }
                }
            }
            11 => {
                v___x_7242_ = lean_nat_dec_le(v___x_7237_, v___x_7237_);
                if v___x_7242_ == 0 {
                    if v___x_7238_ == 0 {
                        leanh::lean_dec_ref(v___x_7241_);
                        leanh::lean_dec_ref(v___x_7234_);
                        v___y_7220_ = v___x_7236_;
                        state = 10;
                        continue;
                    } else {
                        v___x_7243_ = 0usize;
                        v___x_7244_ = lean_usize_of_nat(v___x_7237_);
                        v___x_7245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_7231_, v___x_7234_, v___x_7243_, v___x_7244_, v___x_7241_);
                        leanh::lean_dec_ref(v___x_7234_);
                        v_snd_7246_ = leanh::lean_ctor_get(v___x_7245_, 1);
                        leanh::lean_inc(v_snd_7246_);
                        leanh::lean_dec_ref(v___x_7245_);
                        v___y_7220_ = v_snd_7246_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___x_7247_ = 0usize;
                    v___x_7248_ = lean_usize_of_nat(v___x_7237_);
                    v___x_7249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_expandDeclId_spec__4(v___x_7231_, v___x_7234_, v___x_7247_, v___x_7248_, v___x_7241_);
                    leanh::lean_dec_ref(v___x_7234_);
                    v_snd_7250_ = leanh::lean_ctor_get(v___x_7249_, 1);
                    leanh::lean_inc(v_snd_7250_);
                    leanh::lean_dec_ref(v___x_7249_);
                    v___y_7220_ = v_snd_7250_;
                    state = 10;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_expandDeclId___boxed(
    mut v_currNamespace_7253_: *mut leanh::LeanObject,
    mut v_currLevelNames_7254_: *mut leanh::LeanObject,
    mut v_declId_7255_: *mut leanh::LeanObject,
    mut v_modifiers_7256_: *mut leanh::LeanObject,
    mut v_a_7257_: *mut leanh::LeanObject,
    mut v_a_7258_: *mut leanh::LeanObject,
    mut v_a_7259_: *mut leanh::LeanObject,
    mut v_a_7260_: *mut leanh::LeanObject,
    mut v_a_7261_: *mut leanh::LeanObject,
    mut v_a_7262_: *mut leanh::LeanObject,
    mut v_a_7263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7264_ = l_Lean_Elab_expandDeclId(
        v_currNamespace_7253_,
        v_currLevelNames_7254_,
        v_declId_7255_,
        v_modifiers_7256_,
        v_a_7257_,
        v_a_7258_,
        v_a_7259_,
        v_a_7260_,
        v_a_7261_,
        v_a_7262_,
    );
    leanh::lean_dec(v_a_7262_);
    leanh::lean_dec_ref(v_a_7261_);
    leanh::lean_dec(v_a_7260_);
    leanh::lean_dec_ref(v_a_7259_);
    leanh::lean_dec(v_a_7258_);
    leanh::lean_dec_ref(v_a_7257_);
    leanh::lean_dec_ref(v_modifiers_7256_);
    leanh::lean_dec(v_declId_7255_);
    return v_res_7264_;
}
pub unsafe fn l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(
    mut v_00_u03b1_7265_: *mut leanh::LeanObject,
    mut v_u_7266_: *mut leanh::LeanObject,
    mut v___y_7267_: *mut leanh::LeanObject,
    mut v___y_7268_: *mut leanh::LeanObject,
    mut v___y_7269_: *mut leanh::LeanObject,
    mut v___y_7270_: *mut leanh::LeanObject,
    mut v___y_7271_: *mut leanh::LeanObject,
    mut v___y_7272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7274_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___redArg(v_u_7266_, v___y_7267_, v___y_7268_, v___y_7269_, v___y_7270_, v___y_7271_, v___y_7272_);
    return v___x_7274_;
}
pub unsafe fn l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1___boxed(
    mut v_00_u03b1_7275_: *mut leanh::LeanObject,
    mut v_u_7276_: *mut leanh::LeanObject,
    mut v___y_7277_: *mut leanh::LeanObject,
    mut v___y_7278_: *mut leanh::LeanObject,
    mut v___y_7279_: *mut leanh::LeanObject,
    mut v___y_7280_: *mut leanh::LeanObject,
    mut v___y_7281_: *mut leanh::LeanObject,
    mut v___y_7282_: *mut leanh::LeanObject,
    mut v___y_7283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7284_ =
        l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1(
            v_00_u03b1_7275_,
            v_u_7276_,
            v___y_7277_,
            v___y_7278_,
            v___y_7279_,
            v___y_7280_,
            v___y_7281_,
            v___y_7282_,
        );
    leanh::lean_dec(v___y_7282_);
    leanh::lean_dec_ref(v___y_7281_);
    leanh::lean_dec(v___y_7280_);
    leanh::lean_dec_ref(v___y_7279_);
    leanh::lean_dec(v___y_7278_);
    leanh::lean_dec_ref(v___y_7277_);
    return v_res_7284_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(
    mut v_00_u03b1_7285_: *mut leanh::LeanObject,
    mut v_msg_7286_: *mut leanh::LeanObject,
    mut v___y_7287_: *mut leanh::LeanObject,
    mut v___y_7288_: *mut leanh::LeanObject,
    mut v___y_7289_: *mut leanh::LeanObject,
    mut v___y_7290_: *mut leanh::LeanObject,
    mut v___y_7291_: *mut leanh::LeanObject,
    mut v___y_7292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7294_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___redArg(v_msg_7286_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_);
    return v___x_7294_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1___boxed(
    mut v_00_u03b1_7295_: *mut leanh::LeanObject,
    mut v_msg_7296_: *mut leanh::LeanObject,
    mut v___y_7297_: *mut leanh::LeanObject,
    mut v___y_7298_: *mut leanh::LeanObject,
    mut v___y_7299_: *mut leanh::LeanObject,
    mut v___y_7300_: *mut leanh::LeanObject,
    mut v___y_7301_: *mut leanh::LeanObject,
    mut v___y_7302_: *mut leanh::LeanObject,
    mut v___y_7303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7304_ = l_Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1(v_00_u03b1_7295_, v_msg_7296_, v___y_7297_, v___y_7298_, v___y_7299_, v___y_7300_, v___y_7301_, v___y_7302_);
    leanh::lean_dec(v___y_7302_);
    leanh::lean_dec_ref(v___y_7301_);
    leanh::lean_dec(v___y_7300_);
    leanh::lean_dec_ref(v___y_7299_);
    leanh::lean_dec(v___y_7298_);
    leanh::lean_dec_ref(v___y_7297_);
    return v_res_7304_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(
    mut v_msgData_7305_: *mut leanh::LeanObject,
    mut v_macroStack_7306_: *mut leanh::LeanObject,
    mut v___y_7307_: *mut leanh::LeanObject,
    mut v___y_7308_: *mut leanh::LeanObject,
    mut v___y_7309_: *mut leanh::LeanObject,
    mut v___y_7310_: *mut leanh::LeanObject,
    mut v___y_7311_: *mut leanh::LeanObject,
    mut v___y_7312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7314_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___redArg(v_msgData_7305_, v_macroStack_7306_, v___y_7311_);
    return v___x_7314_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3___boxed(
    mut v_msgData_7315_: *mut leanh::LeanObject,
    mut v_macroStack_7316_: *mut leanh::LeanObject,
    mut v___y_7317_: *mut leanh::LeanObject,
    mut v___y_7318_: *mut leanh::LeanObject,
    mut v___y_7319_: *mut leanh::LeanObject,
    mut v___y_7320_: *mut leanh::LeanObject,
    mut v___y_7321_: *mut leanh::LeanObject,
    mut v___y_7322_: *mut leanh::LeanObject,
    mut v___y_7323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7324_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___00Lean_Elab_expandDeclId_spec__1_spec__1_spec__3(v_msgData_7315_, v_macroStack_7316_, v___y_7317_, v___y_7318_, v___y_7319_, v___y_7320_, v___y_7321_, v___y_7322_);
    leanh::lean_dec(v___y_7322_);
    leanh::lean_dec_ref(v___y_7321_);
    leanh::lean_dec(v___y_7320_);
    leanh::lean_dec_ref(v___y_7319_);
    leanh::lean_dec(v___y_7318_);
    leanh::lean_dec_ref(v___y_7317_);
    return v_res_7324_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(
    mut v_t_7325_: *mut leanh::LeanObject,
    mut v___y_7326_: *mut leanh::LeanObject,
    mut v___y_7327_: *mut leanh::LeanObject,
    mut v___y_7328_: *mut leanh::LeanObject,
    mut v___y_7329_: *mut leanh::LeanObject,
    mut v___y_7330_: *mut leanh::LeanObject,
    mut v___y_7331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7333_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___redArg(v_t_7325_, v___y_7331_);
    return v___x_7333_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17___boxed(
    mut v_t_7334_: *mut leanh::LeanObject,
    mut v___y_7335_: *mut leanh::LeanObject,
    mut v___y_7336_: *mut leanh::LeanObject,
    mut v___y_7337_: *mut leanh::LeanObject,
    mut v___y_7338_: *mut leanh::LeanObject,
    mut v___y_7339_: *mut leanh::LeanObject,
    mut v___y_7340_: *mut leanh::LeanObject,
    mut v___y_7341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7342_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__14_spec__17(v_t_7334_, v___y_7335_, v___y_7336_, v___y_7337_, v___y_7338_, v___y_7339_, v___y_7340_);
    leanh::lean_dec(v___y_7340_);
    leanh::lean_dec_ref(v___y_7339_);
    leanh::lean_dec(v___y_7338_);
    leanh::lean_dec_ref(v___y_7337_);
    leanh::lean_dec(v___y_7336_);
    leanh::lean_dec_ref(v___y_7335_);
    return v_res_7342_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(
    mut v_env_7343_: *mut leanh::LeanObject,
    mut v___y_7344_: *mut leanh::LeanObject,
    mut v___y_7345_: *mut leanh::LeanObject,
    mut v___y_7346_: *mut leanh::LeanObject,
    mut v___y_7347_: *mut leanh::LeanObject,
    mut v___y_7348_: *mut leanh::LeanObject,
    mut v___y_7349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7351_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___redArg(v_env_7343_, v___y_7347_, v___y_7349_);
    return v___x_7351_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19___boxed(
    mut v_env_7352_: *mut leanh::LeanObject,
    mut v___y_7353_: *mut leanh::LeanObject,
    mut v___y_7354_: *mut leanh::LeanObject,
    mut v___y_7355_: *mut leanh::LeanObject,
    mut v___y_7356_: *mut leanh::LeanObject,
    mut v___y_7357_: *mut leanh::LeanObject,
    mut v___y_7358_: *mut leanh::LeanObject,
    mut v___y_7359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7360_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15_spec__19(v_env_7352_, v___y_7353_, v___y_7354_, v___y_7355_, v___y_7356_, v___y_7357_, v___y_7358_);
    leanh::lean_dec(v___y_7358_);
    leanh::lean_dec_ref(v___y_7357_);
    leanh::lean_dec(v___y_7356_);
    leanh::lean_dec_ref(v___y_7355_);
    leanh::lean_dec(v___y_7354_);
    leanh::lean_dec_ref(v___y_7353_);
    return v_res_7360_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(
    mut v_00_u03b1_7361_: *mut leanh::LeanObject,
    mut v_env_7362_: *mut leanh::LeanObject,
    mut v_x_7363_: *mut leanh::LeanObject,
    mut v___y_7364_: *mut leanh::LeanObject,
    mut v___y_7365_: *mut leanh::LeanObject,
    mut v___y_7366_: *mut leanh::LeanObject,
    mut v___y_7367_: *mut leanh::LeanObject,
    mut v___y_7368_: *mut leanh::LeanObject,
    mut v___y_7369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7371_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___redArg(v_env_7362_, v_x_7363_, v___y_7364_, v___y_7365_, v___y_7366_, v___y_7367_, v___y_7368_, v___y_7369_);
    return v___x_7371_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15___boxed(
    mut v_00_u03b1_7372_: *mut leanh::LeanObject,
    mut v_env_7373_: *mut leanh::LeanObject,
    mut v_x_7374_: *mut leanh::LeanObject,
    mut v___y_7375_: *mut leanh::LeanObject,
    mut v___y_7376_: *mut leanh::LeanObject,
    mut v___y_7377_: *mut leanh::LeanObject,
    mut v___y_7378_: *mut leanh::LeanObject,
    mut v___y_7379_: *mut leanh::LeanObject,
    mut v___y_7380_: *mut leanh::LeanObject,
    mut v___y_7381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7382_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__15(v_00_u03b1_7372_, v_env_7373_, v_x_7374_, v___y_7375_, v___y_7376_, v___y_7377_, v___y_7378_, v___y_7379_, v___y_7380_);
    leanh::lean_dec(v___y_7380_);
    leanh::lean_dec_ref(v___y_7379_);
    leanh::lean_dec(v___y_7378_);
    leanh::lean_dec_ref(v___y_7377_);
    leanh::lean_dec(v___y_7376_);
    leanh::lean_dec_ref(v___y_7375_);
    return v_res_7382_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(
    mut v_00_u03b1_7383_: *mut leanh::LeanObject,
    mut v_constName_7384_: *mut leanh::LeanObject,
    mut v___y_7385_: *mut leanh::LeanObject,
    mut v___y_7386_: *mut leanh::LeanObject,
    mut v___y_7387_: *mut leanh::LeanObject,
    mut v___y_7388_: *mut leanh::LeanObject,
    mut v___y_7389_: *mut leanh::LeanObject,
    mut v___y_7390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7392_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___redArg(v_constName_7384_, v___y_7385_, v___y_7386_, v___y_7387_, v___y_7388_, v___y_7389_, v___y_7390_);
    return v___x_7392_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15___boxed(
    mut v_00_u03b1_7393_: *mut leanh::LeanObject,
    mut v_constName_7394_: *mut leanh::LeanObject,
    mut v___y_7395_: *mut leanh::LeanObject,
    mut v___y_7396_: *mut leanh::LeanObject,
    mut v___y_7397_: *mut leanh::LeanObject,
    mut v___y_7398_: *mut leanh::LeanObject,
    mut v___y_7399_: *mut leanh::LeanObject,
    mut v___y_7400_: *mut leanh::LeanObject,
    mut v___y_7401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7402_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15(v_00_u03b1_7393_, v_constName_7394_, v___y_7395_, v___y_7396_, v___y_7397_, v___y_7398_, v___y_7399_, v___y_7400_);
    leanh::lean_dec(v___y_7400_);
    leanh::lean_dec_ref(v___y_7399_);
    leanh::lean_dec(v___y_7398_);
    leanh::lean_dec_ref(v___y_7397_);
    leanh::lean_dec(v___y_7396_);
    leanh::lean_dec_ref(v___y_7395_);
    return v_res_7402_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(
    mut v_00_u03b1_7403_: *mut leanh::LeanObject,
    mut v_ref_7404_: *mut leanh::LeanObject,
    mut v_constName_7405_: *mut leanh::LeanObject,
    mut v___y_7406_: *mut leanh::LeanObject,
    mut v___y_7407_: *mut leanh::LeanObject,
    mut v___y_7408_: *mut leanh::LeanObject,
    mut v___y_7409_: *mut leanh::LeanObject,
    mut v___y_7410_: *mut leanh::LeanObject,
    mut v___y_7411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7413_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___redArg(v_ref_7404_, v_constName_7405_, v___y_7406_, v___y_7407_, v___y_7408_, v___y_7409_, v___y_7410_, v___y_7411_);
    return v___x_7413_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20___boxed(
    mut v_00_u03b1_7414_: *mut leanh::LeanObject,
    mut v_ref_7415_: *mut leanh::LeanObject,
    mut v_constName_7416_: *mut leanh::LeanObject,
    mut v___y_7417_: *mut leanh::LeanObject,
    mut v___y_7418_: *mut leanh::LeanObject,
    mut v___y_7419_: *mut leanh::LeanObject,
    mut v___y_7420_: *mut leanh::LeanObject,
    mut v___y_7421_: *mut leanh::LeanObject,
    mut v___y_7422_: *mut leanh::LeanObject,
    mut v___y_7423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7424_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20(v_00_u03b1_7414_, v_ref_7415_, v_constName_7416_, v___y_7417_, v___y_7418_, v___y_7419_, v___y_7420_, v___y_7421_, v___y_7422_);
    leanh::lean_dec(v___y_7422_);
    leanh::lean_dec_ref(v___y_7421_);
    leanh::lean_dec(v___y_7420_);
    leanh::lean_dec_ref(v___y_7419_);
    leanh::lean_dec(v___y_7418_);
    leanh::lean_dec_ref(v___y_7417_);
    leanh::lean_dec(v_ref_7415_);
    return v_res_7424_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(
    mut v_00_u03b1_7425_: *mut leanh::LeanObject,
    mut v_ref_7426_: *mut leanh::LeanObject,
    mut v_msg_7427_: *mut leanh::LeanObject,
    mut v_declHint_7428_: *mut leanh::LeanObject,
    mut v___y_7429_: *mut leanh::LeanObject,
    mut v___y_7430_: *mut leanh::LeanObject,
    mut v___y_7431_: *mut leanh::LeanObject,
    mut v___y_7432_: *mut leanh::LeanObject,
    mut v___y_7433_: *mut leanh::LeanObject,
    mut v___y_7434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7436_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___redArg(v_ref_7426_, v_msg_7427_, v_declHint_7428_, v___y_7429_, v___y_7430_, v___y_7431_, v___y_7432_, v___y_7433_, v___y_7434_);
    return v___x_7436_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22___boxed(
    mut v_00_u03b1_7437_: *mut leanh::LeanObject,
    mut v_ref_7438_: *mut leanh::LeanObject,
    mut v_msg_7439_: *mut leanh::LeanObject,
    mut v_declHint_7440_: *mut leanh::LeanObject,
    mut v___y_7441_: *mut leanh::LeanObject,
    mut v___y_7442_: *mut leanh::LeanObject,
    mut v___y_7443_: *mut leanh::LeanObject,
    mut v___y_7444_: *mut leanh::LeanObject,
    mut v___y_7445_: *mut leanh::LeanObject,
    mut v___y_7446_: *mut leanh::LeanObject,
    mut v___y_7447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7448_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22(v_00_u03b1_7437_, v_ref_7438_, v_msg_7439_, v_declHint_7440_, v___y_7441_, v___y_7442_, v___y_7443_, v___y_7444_, v___y_7445_, v___y_7446_);
    leanh::lean_dec(v___y_7446_);
    leanh::lean_dec_ref(v___y_7445_);
    leanh::lean_dec(v___y_7444_);
    leanh::lean_dec_ref(v___y_7443_);
    leanh::lean_dec(v___y_7442_);
    leanh::lean_dec_ref(v___y_7441_);
    leanh::lean_dec(v_ref_7438_);
    return v_res_7448_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(
    mut v_msg_7449_: *mut leanh::LeanObject,
    mut v_declHint_7450_: *mut leanh::LeanObject,
    mut v___y_7451_: *mut leanh::LeanObject,
    mut v___y_7452_: *mut leanh::LeanObject,
    mut v___y_7453_: *mut leanh::LeanObject,
    mut v___y_7454_: *mut leanh::LeanObject,
    mut v___y_7455_: *mut leanh::LeanObject,
    mut v___y_7456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7458_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___redArg(v_msg_7449_, v_declHint_7450_, v___y_7456_);
    return v___x_7458_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24___boxed(
    mut v_msg_7459_: *mut leanh::LeanObject,
    mut v_declHint_7460_: *mut leanh::LeanObject,
    mut v___y_7461_: *mut leanh::LeanObject,
    mut v___y_7462_: *mut leanh::LeanObject,
    mut v___y_7463_: *mut leanh::LeanObject,
    mut v___y_7464_: *mut leanh::LeanObject,
    mut v___y_7465_: *mut leanh::LeanObject,
    mut v___y_7466_: *mut leanh::LeanObject,
    mut v___y_7467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7468_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__23_spec__24(v_msg_7459_, v_declHint_7460_, v___y_7461_, v___y_7462_, v___y_7463_, v___y_7464_, v___y_7465_, v___y_7466_);
    leanh::lean_dec(v___y_7466_);
    leanh::lean_dec_ref(v___y_7465_);
    leanh::lean_dec(v___y_7464_);
    leanh::lean_dec_ref(v___y_7463_);
    leanh::lean_dec(v___y_7462_);
    leanh::lean_dec_ref(v___y_7461_);
    return v_res_7468_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(
    mut v_00_u03b1_7469_: *mut leanh::LeanObject,
    mut v_ref_7470_: *mut leanh::LeanObject,
    mut v_msg_7471_: *mut leanh::LeanObject,
    mut v___y_7472_: *mut leanh::LeanObject,
    mut v___y_7473_: *mut leanh::LeanObject,
    mut v___y_7474_: *mut leanh::LeanObject,
    mut v___y_7475_: *mut leanh::LeanObject,
    mut v___y_7476_: *mut leanh::LeanObject,
    mut v___y_7477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7479_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___redArg(v_ref_7470_, v_msg_7471_, v___y_7472_, v___y_7473_, v___y_7474_, v___y_7475_, v___y_7476_, v___y_7477_);
    return v___x_7479_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24___boxed(
    mut v_00_u03b1_7480_: *mut leanh::LeanObject,
    mut v_ref_7481_: *mut leanh::LeanObject,
    mut v_msg_7482_: *mut leanh::LeanObject,
    mut v___y_7483_: *mut leanh::LeanObject,
    mut v___y_7484_: *mut leanh::LeanObject,
    mut v___y_7485_: *mut leanh::LeanObject,
    mut v___y_7486_: *mut leanh::LeanObject,
    mut v___y_7487_: *mut leanh::LeanObject,
    mut v___y_7488_: *mut leanh::LeanObject,
    mut v___y_7489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7490_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00Lean_Elab_applyVisibility___at___00Lean_Elab_mkDeclName___at___00Lean_Elab_expandDeclId_spec__2_spec__4_spec__8_spec__13_spec__14_spec__15_spec__20_spec__22_spec__24(v_00_u03b1_7480_, v_ref_7481_, v_msg_7482_, v___y_7483_, v___y_7484_, v___y_7485_, v___y_7486_, v___y_7487_, v___y_7488_);
    leanh::lean_dec(v___y_7488_);
    leanh::lean_dec_ref(v___y_7487_);
    leanh::lean_dec(v___y_7486_);
    leanh::lean_dec_ref(v___y_7485_);
    leanh::lean_dec(v___y_7484_);
    leanh::lean_dec_ref(v___y_7483_);
    leanh::lean_dec(v_ref_7481_);
    return v_res_7490_;
}
pub unsafe fn l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(
    mut v_x_7494_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_7495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7497_: u8 = 0;
    v_name_7495_ = leanh::lean_ctor_get(v_x_7494_, 0);
    v___x_7496_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___closed__1;
    v___x_7497_ = lean_name_eq(v_name_7495_, v___x_7496_);
    return v___x_7497_;
}
pub unsafe fn l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0___boxed(
    mut v_x_7498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7499_: u8 = 0;
    let mut v_r_7500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7499_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__0(v_x_7498_);
    leanh::lean_dec_ref(v_x_7498_);
    v_r_7500_ = leanh::lean_box((v_res_7499_) as usize);
    return v_r_7500_;
}
pub unsafe fn l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___lam__1(
    mut v_ctx_7501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_x3f_7502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_7503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mayPostpone_7504_: u8 = 0;
    let mut v_errToSorry_7505_: u8 = 0;
    let mut v_autoBoundImplicitContext_7506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicitForbidden_7507_: *mut leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_sectionVars_7508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sectionFVars_7509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_implicitLambda_7510_: u8 = 0;
    let mut v_heedElabAsElim_7511_: u8 = 0;
    let mut v_isNoncomputableSection_7512_: u8 = 0;
    let mut v_isMetaSection_7513_: u8 = 0;
    let mut v_ignoreTCFailures_7514_: u8 = 0;
    let mut v_inPattern_7515_: u8 = 0;
    let mut v_tacSnap_x3f_7516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveRecAppSyntax_7517_: u8 = 0;
    let mut v_holesAsSyntheticOpaque_7518_: u8 = 0;
    let mut v_fixedTermElabs_7519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7522_: u8 = 0;
    let mut v___x_7523_: u8 = 0;
    let mut v___x_7525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_x3f_7502_ = leanh::lean_ctor_get(v_ctx_7501_, 0);
                v_macroStack_7503_ = leanh::lean_ctor_get(v_ctx_7501_, 1);
                v_mayPostpone_7504_ = leanh::lean_ctor_get_uint8(
                    v_ctx_7501_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                v_errToSorry_7505_ = leanh::lean_ctor_get_uint8(
                    v_ctx_7501_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 1) as u32,
                );
                v_autoBoundImplicitContext_7506_ = leanh::lean_ctor_get(v_ctx_7501_, 2);
                v_autoBoundImplicitForbidden_7507_ = leanh::lean_ctor_get(v_ctx_7501_, 3);
                v_sectionVars_7508_ = leanh::lean_ctor_get(v_ctx_7501_, 4);
                v_sectionFVars_7509_ = leanh::lean_ctor_get(v_ctx_7501_, 5);
                v_implicitLambda_7510_ = leanh::lean_ctor_get_uint8(
                    v_ctx_7501_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                );
                v_heedElabAsElim_7511_ = leanh::lean_ctor_get_uint8(
                    v_ctx_7501_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 3) as u32,
                );
                v_isNoncomputableSection_7512_ = leanh::lean_ctor_get_uint8(
                    v_ctx_7501_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 4) as u32,
                );
                v_isMetaSection_7513_ = leanh::lean_ctor_get_uint8(
                    v_ctx_7501_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 5) as u32,
                );
                v_ignoreTCFailures_7514_ = leanh::lean_ctor_get_uint8(
                    v_ctx_7501_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 6) as u32,
                );
                v_inPattern_7515_ = leanh::lean_ctor_get_uint8(
                    v_ctx_7501_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 7) as u32,
                );
                v_tacSnap_x3f_7516_ = leanh::lean_ctor_get(v_ctx_7501_, 6);
                v_saveRecAppSyntax_7517_ = leanh::lean_ctor_get_uint8(
                    v_ctx_7501_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 8) as u32,
                );
                v_holesAsSyntheticOpaque_7518_ = leanh::lean_ctor_get_uint8(
                    v_ctx_7501_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 9) as u32,
                );
                v_fixedTermElabs_7519_ = leanh::lean_ctor_get(v_ctx_7501_, 7);
                v_isSharedCheck_7527_ = (!leanh::lean_is_exclusive(v_ctx_7501_)) as u8;
                if v_isSharedCheck_7527_ == 0 {
                    v___x_7521_ = v_ctx_7501_;
                    v_isShared_7522_ = v_isSharedCheck_7527_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fixedTermElabs_7519_);
                    leanh::lean_inc(v_tacSnap_x3f_7516_);
                    leanh::lean_inc(v_sectionFVars_7509_);
                    leanh::lean_inc(v_sectionVars_7508_);
                    leanh::lean_inc(v_autoBoundImplicitForbidden_7507_);
                    leanh::lean_inc(v_autoBoundImplicitContext_7506_);
                    leanh::lean_inc(v_macroStack_7503_);
                    leanh::lean_inc(v_declName_x3f_7502_);
                    leanh::lean_dec(v_ctx_7501_);
                    v___x_7521_ = leanh::lean_box(0);
                    v_isShared_7522_ = v_isSharedCheck_7527_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7523_ = 0;
                if v_isShared_7522_ == 0 {
                    v___x_7525_ = v___x_7521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7526_ = leanh::lean_alloc_ctor(0, 8, (11) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7526_, 0, v_declName_x3f_7502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7526_, 1, v_macroStack_7503_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_7526_,
                        2,
                        v_autoBoundImplicitContext_7506_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_7526_,
                        3,
                        v_autoBoundImplicitForbidden_7507_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_7526_, 4, v_sectionVars_7508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7526_, 5, v_sectionFVars_7509_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7526_, 6, v_tacSnap_x3f_7516_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7526_, 7, v_fixedTermElabs_7519_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7526_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                        v_mayPostpone_7504_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7526_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 1) as u32,
                        v_errToSorry_7505_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7526_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                        v_implicitLambda_7510_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7526_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 3) as u32,
                        v_heedElabAsElim_7511_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7526_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 4) as u32,
                        v_isNoncomputableSection_7512_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7526_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 5) as u32,
                        v_isMetaSection_7513_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7526_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 6) as u32,
                        v_ignoreTCFailures_7514_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7526_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 7) as u32,
                        v_inPattern_7515_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7526_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 8) as u32,
                        v_saveRecAppSyntax_7517_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7526_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 9) as u32,
                        v_holesAsSyntheticOpaque_7518_,
                    );
                    v___x_7525_ = v_reuseFailAlloc_7526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_7525_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 10) as u32,
                    v___x_7523_,
                );
                return v___x_7525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg(
    mut v_inst_7549_: *mut leanh::LeanObject,
    mut v_attrs_7550_: *mut leanh::LeanObject,
    mut v_a_7551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7555_: u8 = 0;
    v___x_7552_ = leanh::lean_unsigned_to_nat(0);
    v___x_7553_ = lean_array_get_size(v_attrs_7550_);
    v___x_7554_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9;
    v___x_7555_ = lean_nat_dec_lt(v___x_7552_, v___x_7553_);
    if v___x_7555_ == 0 {
        leanh::lean_dec_ref(v_attrs_7550_);
        leanh::lean_dec(v_inst_7549_);
        return v_a_7551_;
    } else {
        if v___x_7555_ == 0 {
            leanh::lean_dec_ref(v_attrs_7550_);
            leanh::lean_dec(v_inst_7549_);
            return v_a_7551_;
        } else {
            let mut v___f_7556_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7557_: usize = 0;
            let mut v___x_7558_: usize = 0;
            let mut v___x_7559_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7560_: u8 = 0;
            v___f_7556_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10;
            v___x_7557_ = 0usize;
            v___x_7558_ = lean_usize_of_nat(v___x_7553_);
            v___x_7559_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_7554_,
                v___f_7556_,
                v_attrs_7550_,
                v___x_7557_,
                v___x_7558_,
            );
            v___x_7560_ = (leanh::lean_unbox(v___x_7559_) as u8);
            leanh::lean_dec(v___x_7559_);
            if v___x_7560_ == 0 {
                leanh::lean_dec(v_inst_7549_);
                return v_a_7551_;
            } else {
                let mut v___f_7561_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7562_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___f_7561_ =
                    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11;
                v___x_7562_ = leanh::lean_apply_3(
                    v_inst_7549_,
                    leanh::lean_box(0),
                    v___f_7561_,
                    v_a_7551_,
                );
                return v___x_7562_;
            }
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withDeprecationContextFromAttrs(
    mut v_m_7563_: *mut leanh::LeanObject,
    mut v_00_u03b1_7564_: *mut leanh::LeanObject,
    mut v_inst_7565_: *mut leanh::LeanObject,
    mut v_attrs_7566_: *mut leanh::LeanObject,
    mut v_a_7567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7571_: u8 = 0;
    v___x_7568_ = leanh::lean_unsigned_to_nat(0);
    v___x_7569_ = lean_array_get_size(v_attrs_7566_);
    v___x_7570_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__9;
    v___x_7571_ = lean_nat_dec_lt(v___x_7568_, v___x_7569_);
    if v___x_7571_ == 0 {
        leanh::lean_dec_ref(v_attrs_7566_);
        leanh::lean_dec(v_inst_7565_);
        return v_a_7567_;
    } else {
        if v___x_7571_ == 0 {
            leanh::lean_dec_ref(v_attrs_7566_);
            leanh::lean_dec(v_inst_7565_);
            return v_a_7567_;
        } else {
            let mut v___f_7572_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7573_: usize = 0;
            let mut v___x_7574_: usize = 0;
            let mut v___x_7575_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7576_: u8 = 0;
            v___f_7572_ = l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__10;
            v___x_7573_ = 0usize;
            v___x_7574_ = lean_usize_of_nat(v___x_7569_);
            v___x_7575_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_7570_,
                v___f_7572_,
                v_attrs_7566_,
                v___x_7573_,
                v___x_7574_,
            );
            v___x_7576_ = (leanh::lean_unbox(v___x_7575_) as u8);
            leanh::lean_dec(v___x_7575_);
            if v___x_7576_ == 0 {
                leanh::lean_dec(v_inst_7565_);
                return v_a_7567_;
            } else {
                let mut v___f_7577_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7578_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___f_7577_ =
                    l_Lean_Elab_Term_withDeprecationContextFromAttrs___redArg___closed__11;
                v___x_7578_ = leanh::lean_apply_3(
                    v_inst_7565_,
                    leanh::lean_box(0),
                    v___f_7577_,
                    v_a_7567_,
                );
                return v___x_7578_;
            }
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DeclModifiers(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_DocString_Add(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_EnvLinter_Nolint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_DeclModifiers_0__Lean_initFn_00___x40_Lean_Elab_DeclModifiers_1403674367____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_linter_redundantVisibility = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_linter_redundantVisibility);
    leanh::lean_dec_ref(res);
    l_Lean_Elab_instInhabitedVisibility_default =
        _init_l_Lean_Elab_instInhabitedVisibility_default();
    l_Lean_Elab_instInhabitedVisibility = _init_l_Lean_Elab_instInhabitedVisibility();
    l_Lean_Elab_instInhabitedRecKind_default = _init_l_Lean_Elab_instInhabitedRecKind_default();
    l_Lean_Elab_instInhabitedRecKind = _init_l_Lean_Elab_instInhabitedRecKind();
    l_Lean_Elab_instInhabitedComputeKind_default =
        _init_l_Lean_Elab_instInhabitedComputeKind_default();
    l_Lean_Elab_instInhabitedComputeKind = _init_l_Lean_Elab_instInhabitedComputeKind();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DeclModifiers(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_DeclModifiers(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_DocString_Add(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_EnvLinter_Nolint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclModifiers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DeclModifiers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_DeclModifiers(builtin);
}