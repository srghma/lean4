// Lean compiler output
// Module: Lake.DSL.Config
// Imports: Lean.Elab.Term Lake.DSL.Extensions Lake.DSL.Syntax Lake.Util.Name
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkApp,
    l_Lean_Syntax_mkCApp, l_Lean_Syntax_mkNameLit, l_Lean_Syntax_mkNumLit, l_Lean_Syntax_mkStrLit,
    l_Lean_TSyntax_getId, l_Lean_mkCIdentFrom, l_Lean_quoteNameMk, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node5,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lake::DSL::DeclUtil::l_Lake_DSL_packageDeclName;
use crate::r#gen::Lake::DSL::Extensions::{
    initialize_Lake_DSL_Extensions, l_Lake_dirExt, l_Lake_nameExt, l_Lake_optsExt,
    runtime_initialize_Lake_DSL_Extensions,
};
use crate::r#gen::Lake::DSL::Syntax::{
    initialize_Lake_DSL_Syntax, runtime_initialize_Lake_DSL_Syntax,
};
use crate::r#gen::Lake::Util::Name::{
    initialize_Lake_Util_Name, l_Lake_Name_quoteFrom, runtime_initialize_Lake_Util_Name,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTerm___boxed, l_Lean_Elab_Term_termElabAttribute,
    l_Lean_Elab_Term_tryPostponeIfNoneOrMVar, l_Lean_Elab_Term_withPushMacroExpansionStack___boxed,
};
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_Environment_contains,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_intercalate,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__1_value:
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
    m_data: [78, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__2_value:
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
    m_data: [110, 117, 109, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13306843946249674491 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__2_value)
            as *mut crate::leanh::LeanObject,
        7229350633979142691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5_value:
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
    m_data: [111, 114, 105, 103, 78, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8_value:
    crate::leanh::LeanStringObject<60> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 60,
    m_capacity: 60,
    m_length: 59,
    m_data: [
        96, 95, 95, 110, 97, 109, 101, 95, 95, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98,
        101, 32, 117, 115, 101, 100, 32, 97, 102, 116, 101, 114, 32, 116, 104, 101, 32, 96, 112,
        97, 99, 107, 97, 103, 101, 96, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 83, 76, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 97, 109, 101, 67, 111, 110, 115, 116, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__2_value) as *mut crate::leanh::LeanObject,12277407653222002017 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__4_value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut crate::leanh::LeanObject,12997130533650095963 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut crate::leanh::LeanObject,11286550318989764116 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__8_value) as *mut crate::leanh::LeanObject,14379505912603517747 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__9_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,13383813871919401118 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__10_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut crate::leanh::LeanObject,3116803351010944398 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut crate::leanh::LeanObject,17570291170315793637 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__13_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 108, 97, 98, 78, 97, 109, 101, 67, 111, 110, 115, 116, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__13_value) as *mut crate::leanh::LeanObject,18216179882849010034 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_dummyDir___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_DSL_dummyDir___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dummyDir___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_dummyDir: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dummyDir___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__0_value:
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
    m_data: [83, 121, 115, 116, 101, 109, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__1_value:
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
    m_data: [70, 105, 108, 101, 80, 97, 116, 104, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__2_value:
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
    m_data: [109, 107, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3794196532276496372 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16862427096323398393 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12740738272846701813 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__4_value:
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
    m_data: [105, 100, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__4_value)
            as *mut crate::leanh::LeanObject,
        6041859491766292191 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__6_value:
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
    m_data: [100, 117, 109, 109, 121, 68, 105, 114, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__6_value)
            as *mut crate::leanh::LeanObject,
        12345917602089148072 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 105, 114, 67, 111, 110, 115, 116, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__0_value) as *mut crate::leanh::LeanObject,14737761738784435815 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 68, 105, 114, 67, 111, 110, 115, 116, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__2_value) as *mut crate::leanh::LeanObject,2474536823929498258 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__0_value:
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
    m_data: [103, 101, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6629962664469725265 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value:
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
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__4_value:
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
    m_data: [97, 112, 112, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_2:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__4_value)
            as *mut crate::leanh::LeanObject,
        12966880221525079621 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6_value:
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
    m_data: [115, 111, 109, 101, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6_value)
            as *mut crate::leanh::LeanObject,
        15308379890181982757 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value:
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
    m_data: [79, 112, 116, 105, 111, 110, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value)
            as *mut crate::leanh::LeanObject,
        18184376426117065311 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6_value)
            as *mut crate::leanh::LeanObject,
        4893146552088433753 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__11_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__11_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__13_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__13_value
        ) as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__15_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__15_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_2:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__15_value
        ) as *mut crate::leanh::LeanObject,
        5346268661279150583 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__17_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__17_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_2:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__17_value
        ) as *mut crate::leanh::LeanObject,
        7306243862518720553 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__20_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__20_value
        ) as *mut crate::leanh::LeanObject,
        9871775667037945883 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__24_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25_value:
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
    m_data: [69, 108, 97, 98, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25_value
        ) as *mut crate::leanh::LeanObject,
        11510100434945111860 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7892421401833366012 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__27_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__27_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25_value
        ) as *mut crate::leanh::LeanObject,
        11510100434945111860 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__29_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__29:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__30_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__31_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__30_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__31:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__32_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__31_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__32:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__33_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__29_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__32_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__33:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__34_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__27_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__33_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__34:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__24_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__34_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36_value
        ) as *mut crate::leanh::LeanObject,
        17416048715816169289 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value)
            as *mut crate::leanh::LeanObject,
        18184376426117065311 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36_value
        ) as *mut crate::leanh::LeanObject,
        9480010471355609749 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__40_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__40:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__40_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value)
            as *mut crate::leanh::LeanObject,
        18184376426117065311 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__45_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__45:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__46_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__46:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__46_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value)
            as *mut crate::leanh::LeanObject,
        3127099019797772086 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__48_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__48:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__48_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__49_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__48_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__49:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__49_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__50_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__46_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__49_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__50:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__50_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__45_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__50_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52_value:
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
    m_data: [83, 116, 114, 105, 110, 103, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52_value
        ) as *mut crate::leanh::LeanObject,
        3136308715950998022 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        100, 117, 109, 109, 121, 71, 101, 116, 67, 111, 110, 102, 105, 103, 63, 0,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60_value
        ) as *mut crate::leanh::LeanObject,
        6345706506204061227 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_1:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_2:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value:
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
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62_value
        ) as *mut crate::leanh::LeanObject,
        9368229134555052249 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 108, 97, 98, 71, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__0_value) as *mut crate::leanh::LeanObject,1504741952025245079 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5(
    mut v_opts_1086_: *mut crate::leanh::LeanObject,
    mut v_opt_1087_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1088_ = crate::leanh::lean_ctor_get(v_opt_1087_, 0);
    v_defValue_1089_ = crate::leanh::lean_ctor_get(v_opt_1087_, 1);
    v_map_1090_ = crate::leanh::lean_ctor_get(v_opts_1086_, 0);
    v___x_1091_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1090_,
            v_name_1088_,
        );
    if crate::leanh::lean_obj_tag(v___x_1091_) == 0 {
        let mut v___x_1092_: u8 = 0;
        v___x_1092_ = (crate::leanh::lean_unbox(v_defValue_1089_) as u8);
        return v___x_1092_;
    } else {
        let mut v_val_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1093_ = crate::leanh::lean_ctor_get(v___x_1091_, 0);
        crate::leanh::lean_inc(v_val_1093_);
        crate::leanh::lean_dec_ref_known(v___x_1091_, 1);
        if crate::leanh::lean_obj_tag(v_val_1093_) == 1 {
            let mut v_v_1094_: u8 = 0;
            v_v_1094_ = crate::leanh::lean_ctor_get_uint8(v_val_1093_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1093_, 0);
            return v_v_1094_;
        } else {
            let mut v___x_1095_: u8 = 0;
            crate::leanh::lean_dec(v_val_1093_);
            v___x_1095_ = (crate::leanh::lean_unbox(v_defValue_1089_) as u8);
            return v___x_1095_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5___boxed(
    mut v_opts_1096_: *mut crate::leanh::LeanObject,
    mut v_opt_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1098_: u8 = 0;
    let mut v_r_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1098_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5(v_opts_1096_, v_opt_1097_);
    crate::leanh::lean_dec_ref(v_opt_1097_);
    crate::leanh::lean_dec_ref(v_opts_1096_);
    v_r_1099_ = crate::leanh::lean_box((v_res_1098_) as usize);
    return v_r_1099_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1100_ = crate::leanh::lean_box(1);
    v___x_1101_ = l_Lean_MessageData_ofFormat(v___x_1100_);
    return v___x_1101_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__2;
    v___x_1106_ = l_Lean_MessageData_ofFormat(v___x_1105_);
    return v___x_1106_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6(
    mut v_x_1107_: *mut crate::leanh::LeanObject,
    mut v_x_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1113_: u8 = 0;
    let mut v_before_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1117_: u8 = 0;
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut v_unused_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1108_) == 0 {
                    return v_x_1107_;
                } else {
                    v_head_1109_ = crate::leanh::lean_ctor_get(v_x_1108_, 0);
                    v_tail_1110_ = crate::leanh::lean_ctor_get(v_x_1108_, 1);
                    v_isSharedCheck_1132_ = (!crate::leanh::lean_is_exclusive(v_x_1108_)) as u8;
                    if v_isSharedCheck_1132_ == 0 {
                        v___x_1112_ = v_x_1108_;
                        v_isShared_1113_ = v_isSharedCheck_1132_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1110_);
                        crate::leanh::lean_inc(v_head_1109_);
                        crate::leanh::lean_dec(v_x_1108_);
                        v___x_1112_ = crate::leanh::lean_box(0);
                        v_isShared_1113_ = v_isSharedCheck_1132_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1114_ = crate::leanh::lean_ctor_get(v_head_1109_, 0);
                v_isSharedCheck_1130_ = (!crate::leanh::lean_is_exclusive(v_head_1109_)) as u8;
                if v_isSharedCheck_1130_ == 0 {
                    v_unused_1131_ = crate::leanh::lean_ctor_get(v_head_1109_, 1);
                    crate::leanh::lean_dec(v_unused_1131_);
                    v___x_1116_ = v_head_1109_;
                    v_isShared_1117_ = v_isSharedCheck_1130_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_1114_);
                    crate::leanh::lean_dec(v_head_1109_);
                    v___x_1116_ = crate::leanh::lean_box(0);
                    v_isShared_1117_ = v_isSharedCheck_1130_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1118_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0);
                if v_isShared_1117_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1116_, 7);
                    crate::leanh::lean_ctor_set(v___x_1116_, 1, v___x_1118_);
                    crate::leanh::lean_ctor_set(v___x_1116_, 0, v_x_1107_);
                    v___x_1120_ = v___x_1116_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_x_1107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 1, v___x_1118_);
                    v___x_1120_ = v_reuseFailAlloc_1129_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1121_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3);
                if v_isShared_1113_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1112_, 7);
                    crate::leanh::lean_ctor_set(v___x_1112_, 1, v___x_1121_);
                    crate::leanh::lean_ctor_set(v___x_1112_, 0, v___x_1120_);
                    v___x_1123_ = v___x_1112_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1128_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1120_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1121_);
                    v___x_1123_ = v_reuseFailAlloc_1128_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1124_ = l_Lean_MessageData_ofSyntax(v_before_1114_);
                v___x_1125_ = l_Lean_indentD(v___x_1124_);
                v___x_1126_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1126_, 0, v___x_1123_);
                crate::leanh::lean_ctor_set(v___x_1126_, 1, v___x_1125_);
                v_x_1107_ = v___x_1126_;
                v_x_1108_ = v_tail_1110_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1136_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__1;
    v___x_1137_ = l_Lean_MessageData_ofFormat(v___x_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(
    mut v_msgData_1138_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: u8 = 0;
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut v_unused_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1142_ = crate::leanh::lean_ctor_get(v___y_1140_, 2);
                v___x_1143_ = l_Lean_Elab_pp_macroStack;
                v___x_1144_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5(v_options_1142_, v___x_1143_);
                if v___x_1144_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_1139_);
                    v___x_1145_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1145_, 0, v_msgData_1138_);
                    return v___x_1145_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_1139_) == 0 {
                        v___x_1146_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1146_, 0, v_msgData_1138_);
                        return v___x_1146_;
                    } else {
                        v_head_1147_ = crate::leanh::lean_ctor_get(v_macroStack_1139_, 0);
                        crate::leanh::lean_inc(v_head_1147_);
                        v_after_1148_ = crate::leanh::lean_ctor_get(v_head_1147_, 1);
                        v_isSharedCheck_1163_ =
                            (!crate::leanh::lean_is_exclusive(v_head_1147_)) as u8;
                        if v_isSharedCheck_1163_ == 0 {
                            v_unused_1164_ = crate::leanh::lean_ctor_get(v_head_1147_, 0);
                            crate::leanh::lean_dec(v_unused_1164_);
                            v___x_1150_ = v_head_1147_;
                            v_isShared_1151_ = v_isSharedCheck_1163_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_1148_);
                            crate::leanh::lean_dec(v_head_1147_);
                            v___x_1150_ = crate::leanh::lean_box(0);
                            v_isShared_1151_ = v_isSharedCheck_1163_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1152_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0);
                if v_isShared_1151_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1150_, 7);
                    crate::leanh::lean_ctor_set(v___x_1150_, 1, v___x_1152_);
                    crate::leanh::lean_ctor_set(v___x_1150_, 0, v_msgData_1138_);
                    v___x_1154_ = v___x_1150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1162_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_msgData_1138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1152_);
                    v___x_1154_ = v_reuseFailAlloc_1162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1155_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2);
                v___x_1156_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1156_, 0, v___x_1154_);
                crate::leanh::lean_ctor_set(v___x_1156_, 1, v___x_1155_);
                v___x_1157_ = l_Lean_MessageData_ofSyntax(v_after_1148_);
                v___x_1158_ = l_Lean_indentD(v___x_1157_);
                v_msgData_1159_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_1159_, 0, v___x_1156_);
                crate::leanh::lean_ctor_set(v_msgData_1159_, 1, v___x_1158_);
                v___x_1160_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6(v_msgData_1159_, v_macroStack_1139_);
                v___x_1161_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1161_, 0, v___x_1160_);
                return v___x_1161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___boxed(
    mut v_msgData_1165_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1166_: *mut crate::leanh::LeanObject,
    mut v___y_1167_: *mut crate::leanh::LeanObject,
    mut v___y_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1169_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(v_msgData_1165_, v_macroStack_1166_, v___y_1167_);
    crate::leanh::lean_dec_ref(v___y_1167_);
    return v_res_1169_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2(
    mut v_msgData_1170_: *mut crate::leanh::LeanObject,
    mut v___y_1171_: *mut crate::leanh::LeanObject,
    mut v___y_1172_: *mut crate::leanh::LeanObject,
    mut v___y_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1176_ = lean_st_ref_get(v___y_1174_);
    v_env_1177_ = crate::leanh::lean_ctor_get(v___x_1176_, 0);
    crate::leanh::lean_inc_ref(v_env_1177_);
    crate::leanh::lean_dec(v___x_1176_);
    v___x_1178_ = lean_st_ref_get(v___y_1172_);
    v_mctx_1179_ = crate::leanh::lean_ctor_get(v___x_1178_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1179_);
    crate::leanh::lean_dec(v___x_1178_);
    v_lctx_1180_ = crate::leanh::lean_ctor_get(v___y_1171_, 2);
    v_options_1181_ = crate::leanh::lean_ctor_get(v___y_1173_, 2);
    crate::leanh::lean_inc_ref(v_options_1181_);
    crate::leanh::lean_inc_ref(v_lctx_1180_);
    v___x_1182_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1182_, 0, v_env_1177_);
    crate::leanh::lean_ctor_set(v___x_1182_, 1, v_mctx_1179_);
    crate::leanh::lean_ctor_set(v___x_1182_, 2, v_lctx_1180_);
    crate::leanh::lean_ctor_set(v___x_1182_, 3, v_options_1181_);
    v___x_1183_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1183_, 0, v___x_1182_);
    crate::leanh::lean_ctor_set(v___x_1183_, 1, v_msgData_1170_);
    v___x_1184_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1184_, 0, v___x_1183_);
    return v___x_1184_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2___boxed(
    mut v_msgData_1185_: *mut crate::leanh::LeanObject,
    mut v___y_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
    mut v___y_1188_: *mut crate::leanh::LeanObject,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
    mut v___y_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1191_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2(v_msgData_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
    crate::leanh::lean_dec(v___y_1189_);
    crate::leanh::lean_dec_ref(v___y_1188_);
    crate::leanh::lean_dec(v___y_1187_);
    crate::leanh::lean_dec_ref(v___y_1186_);
    return v_res_1191_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(
    mut v_msg_1192_: *mut crate::leanh::LeanObject,
    mut v___y_1193_: *mut crate::leanh::LeanObject,
    mut v___y_1194_: *mut crate::leanh::LeanObject,
    mut v___y_1195_: *mut crate::leanh::LeanObject,
    mut v___y_1196_: *mut crate::leanh::LeanObject,
    mut v___y_1197_: *mut crate::leanh::LeanObject,
    mut v___y_1198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1200_ = crate::leanh::lean_ctor_get(v___y_1197_, 5);
                v___x_1201_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2(v_msg_1192_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
                v_a_1202_ = crate::leanh::lean_ctor_get(v___x_1201_, 0);
                crate::leanh::lean_inc(v_a_1202_);
                crate::leanh::lean_dec_ref(v___x_1201_);
                v_macroStack_1203_ = crate::leanh::lean_ctor_get(v___y_1193_, 1);
                v___x_1204_ = l_Lean_Elab_getBetterRef(v_ref_1200_, v_macroStack_1203_);
                crate::leanh::lean_inc(v_macroStack_1203_);
                v___x_1205_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(v_a_1202_, v_macroStack_1203_, v___y_1197_);
                v_a_1206_ = crate::leanh::lean_ctor_get(v___x_1205_, 0);
                v_isSharedCheck_1214_ = (!crate::leanh::lean_is_exclusive(v___x_1205_)) as u8;
                if v_isSharedCheck_1214_ == 0 {
                    v___x_1208_ = v___x_1205_;
                    v_isShared_1209_ = v_isSharedCheck_1214_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1206_);
                    crate::leanh::lean_dec(v___x_1205_);
                    v___x_1208_ = crate::leanh::lean_box(0);
                    v_isShared_1209_ = v_isSharedCheck_1214_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1210_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1210_, 0, v___x_1204_);
                crate::leanh::lean_ctor_set(v___x_1210_, 1, v_a_1206_);
                if v_isShared_1209_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1208_, 1);
                    crate::leanh::lean_ctor_set(v___x_1208_, 0, v___x_1210_);
                    v___x_1212_ = v___x_1208_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
                    v___x_1212_ = v_reuseFailAlloc_1213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg___boxed(
    mut v_msg_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
    mut v___y_1218_: *mut crate::leanh::LeanObject,
    mut v___y_1219_: *mut crate::leanh::LeanObject,
    mut v___y_1220_: *mut crate::leanh::LeanObject,
    mut v___y_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1223_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v_msg_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
    crate::leanh::lean_dec(v___y_1221_);
    crate::leanh::lean_dec_ref(v___y_1220_);
    crate::leanh::lean_dec(v___y_1219_);
    crate::leanh::lean_dec_ref(v___y_1218_);
    crate::leanh::lean_dec(v___y_1217_);
    crate::leanh::lean_dec_ref(v___y_1216_);
    return v_res_1223_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0(
    mut v_stx_1224_: *mut crate::leanh::LeanObject,
    mut v_output_1225_: *mut crate::leanh::LeanObject,
    mut v_trees_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
    mut v___y_1232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_1234_ = crate::leanh::lean_ctor_get(v___y_1229_, 2);
    crate::leanh::lean_inc_ref(v_lctx_1234_);
    v___x_1235_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1235_, 0, v_lctx_1234_);
    crate::leanh::lean_ctor_set(v___x_1235_, 1, v_stx_1224_);
    crate::leanh::lean_ctor_set(v___x_1235_, 2, v_output_1225_);
    v___x_1236_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1236_, 0, v___x_1235_);
    v___x_1237_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1237_, 0, v___x_1236_);
    crate::leanh::lean_ctor_set(v___x_1237_, 1, v_trees_1226_);
    v___x_1238_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1238_, 0, v___x_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_stx_1239_: *mut crate::leanh::LeanObject,
    mut v_output_1240_: *mut crate::leanh::LeanObject,
    mut v_trees_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
    mut v___y_1248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0(v_stx_1239_, v_output_1240_, v_trees_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
    crate::leanh::lean_dec(v___y_1247_);
    crate::leanh::lean_dec_ref(v___y_1246_);
    crate::leanh::lean_dec(v___y_1245_);
    crate::leanh::lean_dec_ref(v___y_1244_);
    crate::leanh::lean_dec(v___y_1243_);
    crate::leanh::lean_dec_ref(v___y_1242_);
    return v_res_1249_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1250_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1251_ = lean_mk_empty_array_with_capacity(v___x_1250_);
    v___x_1252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1252_, 0, v___x_1251_);
    return v___x_1252_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1253_: usize = 0;
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1253_ = 5usize;
    v___x_1254_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1255_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1256_ = lean_mk_empty_array_with_capacity(v___x_1255_);
    v___x_1257_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
    v___x_1258_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1258_, 0, v___x_1257_);
    crate::leanh::lean_ctor_set(v___x_1258_, 1, v___x_1256_);
    crate::leanh::lean_ctor_set(v___x_1258_, 2, v___x_1254_);
    crate::leanh::lean_ctor_set(v___x_1258_, 3, v___x_1254_);
    crate::leanh::lean_ctor_set_usize(v___x_1258_, 4, v___x_1253_);
    return v___x_1258_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v___y_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v_enabled_1277_: u8 = 0;
    let mut v_assignment_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut v_unused_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1261_ = lean_st_ref_get(v___y_1259_);
                v_infoState_1262_ = crate::leanh::lean_ctor_get(v___x_1261_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1262_);
                crate::leanh::lean_dec(v___x_1261_);
                v_trees_1263_ = crate::leanh::lean_ctor_get(v_infoState_1262_, 2);
                crate::leanh::lean_inc_ref(v_trees_1263_);
                crate::leanh::lean_dec_ref(v_infoState_1262_);
                v___x_1264_ = lean_st_ref_take(v___y_1259_);
                v_infoState_1265_ = crate::leanh::lean_ctor_get(v___x_1264_, 7);
                v_env_1266_ = crate::leanh::lean_ctor_get(v___x_1264_, 0);
                v_nextMacroScope_1267_ = crate::leanh::lean_ctor_get(v___x_1264_, 1);
                v_ngen_1268_ = crate::leanh::lean_ctor_get(v___x_1264_, 2);
                v_auxDeclNGen_1269_ = crate::leanh::lean_ctor_get(v___x_1264_, 3);
                v_traceState_1270_ = crate::leanh::lean_ctor_get(v___x_1264_, 4);
                v_cache_1271_ = crate::leanh::lean_ctor_get(v___x_1264_, 5);
                v_messages_1272_ = crate::leanh::lean_ctor_get(v___x_1264_, 6);
                v_snapshotTasks_1273_ = crate::leanh::lean_ctor_get(v___x_1264_, 8);
                v_isSharedCheck_1294_ = (!crate::leanh::lean_is_exclusive(v___x_1264_)) as u8;
                if v_isSharedCheck_1294_ == 0 {
                    v___x_1275_ = v___x_1264_;
                    v_isShared_1276_ = v_isSharedCheck_1294_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1273_);
                    crate::leanh::lean_inc(v_infoState_1265_);
                    crate::leanh::lean_inc(v_messages_1272_);
                    crate::leanh::lean_inc(v_cache_1271_);
                    crate::leanh::lean_inc(v_traceState_1270_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1269_);
                    crate::leanh::lean_inc(v_ngen_1268_);
                    crate::leanh::lean_inc(v_nextMacroScope_1267_);
                    crate::leanh::lean_inc(v_env_1266_);
                    crate::leanh::lean_dec(v___x_1264_);
                    v___x_1275_ = crate::leanh::lean_box(0);
                    v_isShared_1276_ = v_isSharedCheck_1294_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1277_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1265_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1278_ = crate::leanh::lean_ctor_get(v_infoState_1265_, 0);
                v_lazyAssignment_1279_ = crate::leanh::lean_ctor_get(v_infoState_1265_, 1);
                v_isSharedCheck_1292_ = (!crate::leanh::lean_is_exclusive(v_infoState_1265_)) as u8;
                if v_isSharedCheck_1292_ == 0 {
                    v_unused_1293_ = crate::leanh::lean_ctor_get(v_infoState_1265_, 2);
                    crate::leanh::lean_dec(v_unused_1293_);
                    v___x_1281_ = v_infoState_1265_;
                    v_isShared_1282_ = v_isSharedCheck_1292_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_1279_);
                    crate::leanh::lean_inc(v_assignment_1278_);
                    crate::leanh::lean_dec(v_infoState_1265_);
                    v___x_1281_ = crate::leanh::lean_box(0);
                    v_isShared_1282_ = v_isSharedCheck_1292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1283_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
                if v_isShared_1282_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1281_, 2, v___x_1283_);
                    v___x_1285_ = v___x_1281_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_assignment_1278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_lazyAssignment_1279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 2, v___x_1283_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1291_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_1277_,
                    );
                    v___x_1285_ = v_reuseFailAlloc_1291_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1276_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1275_, 7, v___x_1285_);
                    v___x_1287_ = v___x_1275_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1290_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_env_1266_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_nextMacroScope_1267_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_ngen_1268_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 3, v_auxDeclNGen_1269_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 4, v_traceState_1270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 5, v_cache_1271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 6, v_messages_1272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 7, v___x_1285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 8, v_snapshotTasks_1273_);
                    v___x_1287_ = v_reuseFailAlloc_1290_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1288_ = lean_st_ref_set(v___y_1259_, v___x_1287_);
                v___x_1289_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1289_, 0, v_trees_1263_);
                return v___x_1289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v___y_1295_: *mut crate::leanh::LeanObject,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1297_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1295_);
    crate::leanh::lean_dec(v___y_1295_);
    return v_res_1297_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(
    mut v___y_1298_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v_a_1305_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1315_: u8 = 0;
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1328_: u8 = 0;
    let mut v_enabled_1329_: u8 = 0;
    let mut v_assignment_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1347_: u8 = 0;
    let mut v_unused_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1349_: u8 = 0;
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut v_a_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1354_: u8 = 0;
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1308_ = lean_st_ref_get(v___y_1298_);
                v_infoState_1309_ = crate::leanh::lean_ctor_get(v___x_1308_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1309_);
                crate::leanh::lean_dec(v___x_1308_);
                v_trees_1310_ = crate::leanh::lean_ctor_get(v_infoState_1309_, 2);
                crate::leanh::lean_inc_ref(v_trees_1310_);
                crate::leanh::lean_dec_ref(v_infoState_1309_);
                crate::leanh::lean_inc(v___y_1298_);
                crate::leanh::lean_inc_ref(v___y_1304_);
                crate::leanh::lean_inc(v___y_1303_);
                crate::leanh::lean_inc_ref(v___y_1302_);
                crate::leanh::lean_inc(v___y_1301_);
                crate::leanh::lean_inc_ref(v___y_1300_);
                v___x_1311_ = crate::leanh::lean_apply_8(
                    v_mkInfoTree_1299_,
                    v_trees_1310_,
                    v___y_1300_,
                    v___y_1301_,
                    v___y_1302_,
                    v___y_1303_,
                    v___y_1304_,
                    v___y_1298_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1311_) == 0 {
                    v_a_1312_ = crate::leanh::lean_ctor_get(v___x_1311_, 0);
                    v_isSharedCheck_1350_ = (!crate::leanh::lean_is_exclusive(v___x_1311_)) as u8;
                    if v_isSharedCheck_1350_ == 0 {
                        v___x_1314_ = v___x_1311_;
                        v_isShared_1315_ = v_isSharedCheck_1350_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1312_);
                        crate::leanh::lean_dec(v___x_1311_);
                        v___x_1314_ = crate::leanh::lean_box(0);
                        v_isShared_1315_ = v_isSharedCheck_1350_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_1305_);
                    v_a_1351_ = crate::leanh::lean_ctor_get(v___x_1311_, 0);
                    v_isSharedCheck_1358_ = (!crate::leanh::lean_is_exclusive(v___x_1311_)) as u8;
                    if v_isSharedCheck_1358_ == 0 {
                        v___x_1353_ = v___x_1311_;
                        v_isShared_1354_ = v_isSharedCheck_1358_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1351_);
                        crate::leanh::lean_dec(v___x_1311_);
                        v___x_1353_ = crate::leanh::lean_box(0);
                        v_isShared_1354_ = v_isSharedCheck_1358_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1316_ = lean_st_ref_take(v___y_1298_);
                v_infoState_1317_ = crate::leanh::lean_ctor_get(v___x_1316_, 7);
                v_env_1318_ = crate::leanh::lean_ctor_get(v___x_1316_, 0);
                v_nextMacroScope_1319_ = crate::leanh::lean_ctor_get(v___x_1316_, 1);
                v_ngen_1320_ = crate::leanh::lean_ctor_get(v___x_1316_, 2);
                v_auxDeclNGen_1321_ = crate::leanh::lean_ctor_get(v___x_1316_, 3);
                v_traceState_1322_ = crate::leanh::lean_ctor_get(v___x_1316_, 4);
                v_cache_1323_ = crate::leanh::lean_ctor_get(v___x_1316_, 5);
                v_messages_1324_ = crate::leanh::lean_ctor_get(v___x_1316_, 6);
                v_snapshotTasks_1325_ = crate::leanh::lean_ctor_get(v___x_1316_, 8);
                v_isSharedCheck_1349_ = (!crate::leanh::lean_is_exclusive(v___x_1316_)) as u8;
                if v_isSharedCheck_1349_ == 0 {
                    v___x_1327_ = v___x_1316_;
                    v_isShared_1328_ = v_isSharedCheck_1349_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1325_);
                    crate::leanh::lean_inc(v_infoState_1317_);
                    crate::leanh::lean_inc(v_messages_1324_);
                    crate::leanh::lean_inc(v_cache_1323_);
                    crate::leanh::lean_inc(v_traceState_1322_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1321_);
                    crate::leanh::lean_inc(v_ngen_1320_);
                    crate::leanh::lean_inc(v_nextMacroScope_1319_);
                    crate::leanh::lean_inc(v_env_1318_);
                    crate::leanh::lean_dec(v___x_1316_);
                    v___x_1327_ = crate::leanh::lean_box(0);
                    v_isShared_1328_ = v_isSharedCheck_1349_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_1329_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1317_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1330_ = crate::leanh::lean_ctor_get(v_infoState_1317_, 0);
                v_lazyAssignment_1331_ = crate::leanh::lean_ctor_get(v_infoState_1317_, 1);
                v_isSharedCheck_1347_ = (!crate::leanh::lean_is_exclusive(v_infoState_1317_)) as u8;
                if v_isSharedCheck_1347_ == 0 {
                    v_unused_1348_ = crate::leanh::lean_ctor_get(v_infoState_1317_, 2);
                    crate::leanh::lean_dec(v_unused_1348_);
                    v___x_1333_ = v_infoState_1317_;
                    v_isShared_1334_ = v_isSharedCheck_1347_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_1331_);
                    crate::leanh::lean_inc(v_assignment_1330_);
                    crate::leanh::lean_dec(v_infoState_1317_);
                    v___x_1333_ = crate::leanh::lean_box(0);
                    v_isShared_1334_ = v_isSharedCheck_1347_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1335_ = l_Lean_PersistentArray_push___redArg(v_a_1305_, v_a_1312_);
                if v_isShared_1334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1333_, 2, v___x_1335_);
                    v___x_1337_ = v___x_1333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1346_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_assignment_1330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_lazyAssignment_1331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 2, v___x_1335_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1346_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_1329_,
                    );
                    v___x_1337_ = v_reuseFailAlloc_1346_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1328_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1327_, 7, v___x_1337_);
                    v___x_1339_ = v___x_1327_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1345_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_env_1318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_nextMacroScope_1319_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_ngen_1320_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 3, v_auxDeclNGen_1321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 4, v_traceState_1322_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 5, v_cache_1323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 6, v_messages_1324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 7, v___x_1337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 8, v_snapshotTasks_1325_);
                    v___x_1339_ = v_reuseFailAlloc_1345_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1340_ = lean_st_ref_set(v___y_1298_, v___x_1339_);
                v___x_1341_ = crate::leanh::lean_box(0);
                if v_isShared_1315_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1314_, 0, v___x_1341_);
                    v___x_1343_ = v___x_1314_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1344_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
                    v___x_1343_ = v_reuseFailAlloc_1344_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1343_;
            }
            7 => {
                if v_isShared_1354_ == 0 {
                    v___x_1356_ = v___x_1353_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
                    v___x_1356_ = v_reuseFailAlloc_1357_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0___boxed(
    mut v___y_1359_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
    mut v_a_1366_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1367_: *mut crate::leanh::LeanObject,
    mut v___y_1368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1369_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(v___y_1359_, v_mkInfoTree_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v_a_1366_, v_a_x3f_1367_);
    crate::leanh::lean_dec(v_a_x3f_1367_);
    crate::leanh::lean_dec_ref(v___y_1365_);
    crate::leanh::lean_dec(v___y_1364_);
    crate::leanh::lean_dec_ref(v___y_1363_);
    crate::leanh::lean_dec(v___y_1362_);
    crate::leanh::lean_dec_ref(v___y_1361_);
    crate::leanh::lean_dec(v___y_1359_);
    return v_res_1369_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(
    mut v_x_1370_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1371_: *mut crate::leanh::LeanObject,
    mut v___y_1372_: *mut crate::leanh::LeanObject,
    mut v___y_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
    mut v___y_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_1381_: u8 = 0;
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1389_: u8 = 0;
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1395_: u8 = 0;
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1399_: u8 = 0;
    let mut v_unused_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1404_: u8 = 0;
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1408_: u8 = 0;
    let mut v_reuseFailAlloc_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1410_: u8 = 0;
    let mut v_a_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1416_: u8 = 0;
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_unused_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1425_: u8 = 0;
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1379_ = lean_st_ref_get(v___y_1377_);
                v_infoState_1380_ = crate::leanh::lean_ctor_get(v___x_1379_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1380_);
                crate::leanh::lean_dec(v___x_1379_);
                v_enabled_1381_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1380_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_1380_);
                if v_enabled_1381_ == 0 {
                    crate::leanh::lean_dec_ref(v_mkInfoTree_1371_);
                    crate::leanh::lean_inc(v___y_1377_);
                    crate::leanh::lean_inc_ref(v___y_1376_);
                    crate::leanh::lean_inc(v___y_1375_);
                    crate::leanh::lean_inc_ref(v___y_1374_);
                    crate::leanh::lean_inc(v___y_1373_);
                    crate::leanh::lean_inc_ref(v___y_1372_);
                    v___x_1382_ = crate::leanh::lean_apply_7(
                        v_x_1370_,
                        v___y_1372_,
                        v___y_1373_,
                        v___y_1374_,
                        v___y_1375_,
                        v___y_1376_,
                        v___y_1377_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_1382_;
                } else {
                    v___x_1383_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1377_);
                    v_a_1384_ = crate::leanh::lean_ctor_get(v___x_1383_, 0);
                    crate::leanh::lean_inc(v_a_1384_);
                    crate::leanh::lean_dec_ref(v___x_1383_);
                    crate::leanh::lean_inc(v___y_1377_);
                    crate::leanh::lean_inc_ref(v___y_1376_);
                    crate::leanh::lean_inc(v___y_1375_);
                    crate::leanh::lean_inc_ref(v___y_1374_);
                    crate::leanh::lean_inc(v___y_1373_);
                    crate::leanh::lean_inc_ref(v___y_1372_);
                    v_r_1385_ = crate::leanh::lean_apply_7(
                        v_x_1370_,
                        v___y_1372_,
                        v___y_1373_,
                        v___y_1374_,
                        v___y_1375_,
                        v___y_1376_,
                        v___y_1377_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_1385_) == 0 {
                        v_a_1386_ = crate::leanh::lean_ctor_get(v_r_1385_, 0);
                        v_isSharedCheck_1410_ = (!crate::leanh::lean_is_exclusive(v_r_1385_)) as u8;
                        if v_isSharedCheck_1410_ == 0 {
                            v___x_1388_ = v_r_1385_;
                            v_isShared_1389_ = v_isSharedCheck_1410_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1386_);
                            crate::leanh::lean_dec(v_r_1385_);
                            v___x_1388_ = crate::leanh::lean_box(0);
                            v_isShared_1389_ = v_isSharedCheck_1410_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1411_ = crate::leanh::lean_ctor_get(v_r_1385_, 0);
                        crate::leanh::lean_inc(v_a_1411_);
                        crate::leanh::lean_dec_ref_known(v_r_1385_, 1);
                        v___x_1412_ = crate::leanh::lean_box(0);
                        v___x_1413_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(v___y_1377_, v_mkInfoTree_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v_a_1384_, v___x_1412_);
                        if crate::leanh::lean_obj_tag(v___x_1413_) == 0 {
                            v_isSharedCheck_1420_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1413_)) as u8;
                            if v_isSharedCheck_1420_ == 0 {
                                v_unused_1421_ = crate::leanh::lean_ctor_get(v___x_1413_, 0);
                                crate::leanh::lean_dec(v_unused_1421_);
                                v___x_1415_ = v___x_1413_;
                                v_isShared_1416_ = v_isSharedCheck_1420_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1413_);
                                v___x_1415_ = crate::leanh::lean_box(0);
                                v_isShared_1416_ = v_isSharedCheck_1420_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1411_);
                            v_a_1422_ = crate::leanh::lean_ctor_get(v___x_1413_, 0);
                            v_isSharedCheck_1429_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1413_)) as u8;
                            if v_isSharedCheck_1429_ == 0 {
                                v___x_1424_ = v___x_1413_;
                                v_isShared_1425_ = v_isSharedCheck_1429_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1422_);
                                crate::leanh::lean_dec(v___x_1413_);
                                v___x_1424_ = crate::leanh::lean_box(0);
                                v_isShared_1425_ = v_isSharedCheck_1429_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1386_);
                if v_isShared_1389_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1388_, 1);
                    v___x_1391_ = v___x_1388_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1409_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1386_);
                    v___x_1391_ = v_reuseFailAlloc_1409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1392_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(v___y_1377_, v_mkInfoTree_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v_a_1384_, v___x_1391_);
                crate::leanh::lean_dec_ref(v___x_1391_);
                if crate::leanh::lean_obj_tag(v___x_1392_) == 0 {
                    v_isSharedCheck_1399_ = (!crate::leanh::lean_is_exclusive(v___x_1392_)) as u8;
                    if v_isSharedCheck_1399_ == 0 {
                        v_unused_1400_ = crate::leanh::lean_ctor_get(v___x_1392_, 0);
                        crate::leanh::lean_dec(v_unused_1400_);
                        v___x_1394_ = v___x_1392_;
                        v_isShared_1395_ = v_isSharedCheck_1399_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1392_);
                        v___x_1394_ = crate::leanh::lean_box(0);
                        v_isShared_1395_ = v_isSharedCheck_1399_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1386_);
                    v_a_1401_ = crate::leanh::lean_ctor_get(v___x_1392_, 0);
                    v_isSharedCheck_1408_ = (!crate::leanh::lean_is_exclusive(v___x_1392_)) as u8;
                    if v_isSharedCheck_1408_ == 0 {
                        v___x_1403_ = v___x_1392_;
                        v_isShared_1404_ = v_isSharedCheck_1408_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1401_);
                        crate::leanh::lean_dec(v___x_1392_);
                        v___x_1403_ = crate::leanh::lean_box(0);
                        v_isShared_1404_ = v_isSharedCheck_1408_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1395_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1394_, 0, v_a_1386_);
                    v___x_1397_ = v___x_1394_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1398_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1386_);
                    v___x_1397_ = v_reuseFailAlloc_1398_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1397_;
            }
            5 => {
                if v_isShared_1404_ == 0 {
                    v___x_1406_ = v___x_1403_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1407_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
                    v___x_1406_ = v_reuseFailAlloc_1407_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1406_;
            }
            7 => {
                if v_isShared_1416_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1415_, 1);
                    crate::leanh::lean_ctor_set(v___x_1415_, 0, v_a_1411_);
                    v___x_1418_ = v___x_1415_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1411_);
                    v___x_1418_ = v_reuseFailAlloc_1419_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1418_;
            }
            9 => {
                if v_isShared_1425_ == 0 {
                    v___x_1427_ = v___x_1424_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1428_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
                    v___x_1427_ = v_reuseFailAlloc_1428_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_1430_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
    mut v___y_1437_: *mut crate::leanh::LeanObject,
    mut v___y_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1439_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(v_x_1430_, v_mkInfoTree_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
    crate::leanh::lean_dec(v___y_1437_);
    crate::leanh::lean_dec_ref(v___y_1436_);
    crate::leanh::lean_dec(v___y_1435_);
    crate::leanh::lean_dec_ref(v___y_1434_);
    crate::leanh::lean_dec(v___y_1433_);
    crate::leanh::lean_dec_ref(v___y_1432_);
    return v_res_1439_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(
    mut v_stx_1440_: *mut crate::leanh::LeanObject,
    mut v_output_1441_: *mut crate::leanh::LeanObject,
    mut v_x_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
    mut v___y_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1450_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
    crate::leanh::lean_closure_set(v___f_1450_, 0, v_stx_1440_);
    crate::leanh::lean_closure_set(v___f_1450_, 1, v_output_1441_);
    v___x_1451_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(v_x_1442_, v___f_1450_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
    return v___x_1451_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___boxed(
    mut v_stx_1452_: *mut crate::leanh::LeanObject,
    mut v_output_1453_: *mut crate::leanh::LeanObject,
    mut v_x_1454_: *mut crate::leanh::LeanObject,
    mut v___y_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
    mut v___y_1459_: *mut crate::leanh::LeanObject,
    mut v___y_1460_: *mut crate::leanh::LeanObject,
    mut v___y_1461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1462_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_stx_1452_, v_output_1453_, v_x_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
    crate::leanh::lean_dec(v___y_1460_);
    crate::leanh::lean_dec_ref(v___y_1459_);
    crate::leanh::lean_dec(v___y_1458_);
    crate::leanh::lean_dec_ref(v___y_1457_);
    crate::leanh::lean_dec(v___y_1456_);
    crate::leanh::lean_dec_ref(v___y_1455_);
    return v_res_1462_;
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(
    mut v_beforeStx_1463_: *mut crate::leanh::LeanObject,
    mut v_afterStx_1464_: *mut crate::leanh::LeanObject,
    mut v_x_1465_: *mut crate::leanh::LeanObject,
    mut v___y_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
    mut v___y_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1482_: u8 = 0;
    let mut v_a_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1486_: u8 = 0;
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_afterStx_1464_);
                crate::leanh::lean_inc(v_beforeStx_1463_);
                v___x_1473_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_withPushMacroExpansionStack___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_1473_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1473_, 1, v_beforeStx_1463_);
                crate::leanh::lean_closure_set(v___x_1473_, 2, v_afterStx_1464_);
                crate::leanh::lean_closure_set(v___x_1473_, 3, v_x_1465_);
                v___x_1474_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_beforeStx_1463_, v_afterStx_1464_, v___x_1473_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
                if crate::leanh::lean_obj_tag(v___x_1474_) == 0 {
                    v_a_1475_ = crate::leanh::lean_ctor_get(v___x_1474_, 0);
                    v_isSharedCheck_1482_ = (!crate::leanh::lean_is_exclusive(v___x_1474_)) as u8;
                    if v_isSharedCheck_1482_ == 0 {
                        v___x_1477_ = v___x_1474_;
                        v_isShared_1478_ = v_isSharedCheck_1482_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1475_);
                        crate::leanh::lean_dec(v___x_1474_);
                        v___x_1477_ = crate::leanh::lean_box(0);
                        v_isShared_1478_ = v_isSharedCheck_1482_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1483_ = crate::leanh::lean_ctor_get(v___x_1474_, 0);
                    v_isSharedCheck_1490_ = (!crate::leanh::lean_is_exclusive(v___x_1474_)) as u8;
                    if v_isSharedCheck_1490_ == 0 {
                        v___x_1485_ = v___x_1474_;
                        v_isShared_1486_ = v_isSharedCheck_1490_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1483_);
                        crate::leanh::lean_dec(v___x_1474_);
                        v___x_1485_ = crate::leanh::lean_box(0);
                        v_isShared_1486_ = v_isSharedCheck_1490_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1478_ == 0 {
                    v___x_1480_ = v___x_1477_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1481_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
                    v___x_1480_ = v_reuseFailAlloc_1481_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1480_;
            }
            3 => {
                if v_isShared_1486_ == 0 {
                    v___x_1488_ = v___x_1485_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
                    v___x_1488_ = v_reuseFailAlloc_1489_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1488_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg___boxed(
    mut v_beforeStx_1491_: *mut crate::leanh::LeanObject,
    mut v_afterStx_1492_: *mut crate::leanh::LeanObject,
    mut v_x_1493_: *mut crate::leanh::LeanObject,
    mut v___y_1494_: *mut crate::leanh::LeanObject,
    mut v___y_1495_: *mut crate::leanh::LeanObject,
    mut v___y_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
    mut v___y_1499_: *mut crate::leanh::LeanObject,
    mut v___y_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_beforeStx_1491_, v_afterStx_1492_, v_x_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
    crate::leanh::lean_dec(v___y_1499_);
    crate::leanh::lean_dec_ref(v___y_1498_);
    crate::leanh::lean_dec(v___y_1497_);
    crate::leanh::lean_dec_ref(v___y_1496_);
    crate::leanh::lean_dec(v___y_1495_);
    crate::leanh::lean_dec_ref(v___y_1494_);
    return v_res_1501_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1513_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5;
    v___x_1514_ = l_Lake_DSL_packageDeclName;
    v___x_1515_ = l_Lean_Name_str___override(v___x_1514_, v___x_1513_);
    return v___x_1515_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6),
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6_once
        ),
        _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6,
    );
    v___x_1517_ = lean_mk_syntax_ident(v___x_1516_);
    return v___x_1517_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8;
    v___x_1520_ = l_Lean_stringToMessageData(v___x_1519_);
    return v___x_1520_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst(
    mut v_stx_1521_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_1522_: *mut crate::leanh::LeanObject,
    mut v_a_1523_: *mut crate::leanh::LeanObject,
    mut v_a_1524_: *mut crate::leanh::LeanObject,
    mut v_a_1525_: *mut crate::leanh::LeanObject,
    mut v_a_1526_: *mut crate::leanh::LeanObject,
    mut v_a_1527_: *mut crate::leanh::LeanObject,
    mut v_a_1528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: u8 = 0;
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: u8 = 0;
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1581_: u8 = 0;
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1553_ = lean_st_ref_get(v_a_1528_);
                v_env_1554_ = crate::leanh::lean_ctor_get(v___x_1553_, 0);
                crate::leanh::lean_inc_ref_n(v_env_1554_, 2);
                crate::leanh::lean_dec(v___x_1553_);
                v___x_1555_ = crate::leanh::lean_box(0);
                v___x_1556_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4;
                v___x_1573_ = l_Lake_DSL_packageDeclName;
                v___x_1574_ = 1;
                v___x_1575_ = l_Lean_Environment_contains(v_env_1554_, v___x_1573_, v___x_1574_);
                if v___x_1575_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_1554_);
                    crate::leanh::lean_dec(v_expectedType_x3f_1522_);
                    crate::leanh::lean_dec(v_stx_1521_);
                    v___x_1576_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9_once
                        ),
                        _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9,
                    );
                    v___x_1577_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v___x_1576_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
                    v_a_1578_ = crate::leanh::lean_ctor_get(v___x_1577_, 0);
                    v_isSharedCheck_1585_ = (!crate::leanh::lean_is_exclusive(v___x_1577_)) as u8;
                    if v_isSharedCheck_1585_ == 0 {
                        v___x_1580_ = v___x_1577_;
                        v_isShared_1581_ = v_isSharedCheck_1585_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1578_);
                        crate::leanh::lean_dec(v___x_1577_);
                        v___x_1580_ = crate::leanh::lean_box(0);
                        v_isShared_1581_ = v_isSharedCheck_1585_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_1558_ = v_a_1523_;
                    v___y_1559_ = v_a_1524_;
                    v___y_1560_ = v_a_1525_;
                    v___y_1561_ = v_a_1526_;
                    v___y_1562_ = v_a_1527_;
                    v___y_1563_ = v_a_1528_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1539_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3;
                v___x_1540_ = l_Nat_reprFast(v___y_1532_);
                v___x_1541_ = crate::leanh::lean_box(2);
                v___x_1542_ = l_Lean_Syntax_mkNumLit(v___x_1540_, v___x_1541_);
                v___x_1543_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1544_ = lean_mk_empty_array_with_capacity(v___x_1543_);
                v___x_1545_ = lean_array_push(v___x_1544_, v___y_1538_);
                v___x_1546_ = lean_array_push(v___x_1545_, v___x_1542_);
                v___x_1547_ = l_Lean_Syntax_mkCApp(v___x_1539_, v___x_1546_);
                v___x_1548_ = 1;
                v___x_1549_ = crate::leanh::lean_box((v___x_1548_) as usize);
                v___x_1550_ = crate::leanh::lean_box((v___x_1548_) as usize);
                crate::leanh::lean_inc(v___x_1547_);
                v___x_1551_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_elabTerm___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_1551_, 0, v___x_1547_);
                crate::leanh::lean_closure_set(v___x_1551_, 1, v_expectedType_x3f_1522_);
                crate::leanh::lean_closure_set(v___x_1551_, 2, v___x_1549_);
                crate::leanh::lean_closure_set(v___x_1551_, 3, v___x_1550_);
                v___x_1552_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_1521_, v___x_1547_, v___x_1551_, v___y_1533_, v___y_1536_, v___y_1535_, v___y_1537_, v___y_1534_, v___y_1531_);
                return v___x_1552_;
            }
            2 => {
                v___x_1564_ = l_Lake_nameExt;
                v_asyncMode_1565_ = crate::leanh::lean_ctor_get(v___x_1564_, 2);
                v___x_1566_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1556_,
                        v___x_1564_,
                        v_env_1554_,
                        v_asyncMode_1565_,
                        v___x_1555_,
                    );
                v_snd_1567_ = crate::leanh::lean_ctor_get(v___x_1566_, 1);
                crate::leanh::lean_inc(v_snd_1567_);
                if crate::leanh::lean_obj_tag(v_snd_1567_) == 0 {
                    v_fst_1568_ = crate::leanh::lean_ctor_get(v___x_1566_, 0);
                    crate::leanh::lean_inc(v_fst_1568_);
                    crate::leanh::lean_dec(v___x_1566_);
                    v___x_1569_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7_once
                        ),
                        _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7,
                    );
                    v___y_1531_ = v___y_1563_;
                    v___y_1532_ = v_fst_1568_;
                    v___y_1533_ = v___y_1558_;
                    v___y_1534_ = v___y_1562_;
                    v___y_1535_ = v___y_1560_;
                    v___y_1536_ = v___y_1559_;
                    v___y_1537_ = v___y_1561_;
                    v___y_1538_ = v___x_1569_;
                    state = 1;
                    continue;
                } else {
                    v_fst_1570_ = crate::leanh::lean_ctor_get(v___x_1566_, 0);
                    crate::leanh::lean_inc(v_fst_1570_);
                    crate::leanh::lean_dec(v___x_1566_);
                    v___x_1571_ = 0;
                    crate::leanh::lean_inc(v_stx_1521_);
                    v___x_1572_ = l_Lake_Name_quoteFrom(v_stx_1521_, v_snd_1567_, v___x_1571_);
                    v___y_1531_ = v___y_1563_;
                    v___y_1532_ = v_fst_1570_;
                    v___y_1533_ = v___y_1558_;
                    v___y_1534_ = v___y_1562_;
                    v___y_1535_ = v___y_1560_;
                    v___y_1536_ = v___y_1559_;
                    v___y_1537_ = v___y_1561_;
                    v___y_1538_ = v___x_1572_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_1581_ == 0 {
                    v___x_1583_ = v___x_1580_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
                    v___x_1583_ = v_reuseFailAlloc_1584_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___boxed(
    mut v_stx_1586_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_1587_: *mut crate::leanh::LeanObject,
    mut v_a_1588_: *mut crate::leanh::LeanObject,
    mut v_a_1589_: *mut crate::leanh::LeanObject,
    mut v_a_1590_: *mut crate::leanh::LeanObject,
    mut v_a_1591_: *mut crate::leanh::LeanObject,
    mut v_a_1592_: *mut crate::leanh::LeanObject,
    mut v_a_1593_: *mut crate::leanh::LeanObject,
    mut v_a_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1595_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst(
        v_stx_1586_,
        v_expectedType_x3f_1587_,
        v_a_1588_,
        v_a_1589_,
        v_a_1590_,
        v_a_1591_,
        v_a_1592_,
        v_a_1593_,
    );
    crate::leanh::lean_dec(v_a_1593_);
    crate::leanh::lean_dec_ref(v_a_1592_);
    crate::leanh::lean_dec(v_a_1591_);
    crate::leanh::lean_dec_ref(v_a_1590_);
    crate::leanh::lean_dec(v_a_1589_);
    crate::leanh::lean_dec_ref(v_a_1588_);
    return v_res_1595_;
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0(
    mut v_00_u03b1_1596_: *mut crate::leanh::LeanObject,
    mut v_beforeStx_1597_: *mut crate::leanh::LeanObject,
    mut v_afterStx_1598_: *mut crate::leanh::LeanObject,
    mut v_x_1599_: *mut crate::leanh::LeanObject,
    mut v___y_1600_: *mut crate::leanh::LeanObject,
    mut v___y_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
    mut v___y_1604_: *mut crate::leanh::LeanObject,
    mut v___y_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1607_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_beforeStx_1597_, v_afterStx_1598_, v_x_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
    return v___x_1607_;
}
pub unsafe fn l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___boxed(
    mut v_00_u03b1_1608_: *mut crate::leanh::LeanObject,
    mut v_beforeStx_1609_: *mut crate::leanh::LeanObject,
    mut v_afterStx_1610_: *mut crate::leanh::LeanObject,
    mut v_x_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1619_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0(v_00_u03b1_1608_, v_beforeStx_1609_, v_afterStx_1610_, v_x_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
    crate::leanh::lean_dec(v___y_1617_);
    crate::leanh::lean_dec_ref(v___y_1616_);
    crate::leanh::lean_dec(v___y_1615_);
    crate::leanh::lean_dec_ref(v___y_1614_);
    crate::leanh::lean_dec(v___y_1613_);
    crate::leanh::lean_dec_ref(v___y_1612_);
    return v_res_1619_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1(
    mut v_00_u03b1_1620_: *mut crate::leanh::LeanObject,
    mut v_msg_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
    mut v___y_1626_: *mut crate::leanh::LeanObject,
    mut v___y_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v_msg_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
    return v___x_1629_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___boxed(
    mut v_00_u03b1_1630_: *mut crate::leanh::LeanObject,
    mut v_msg_1631_: *mut crate::leanh::LeanObject,
    mut v___y_1632_: *mut crate::leanh::LeanObject,
    mut v___y_1633_: *mut crate::leanh::LeanObject,
    mut v___y_1634_: *mut crate::leanh::LeanObject,
    mut v___y_1635_: *mut crate::leanh::LeanObject,
    mut v___y_1636_: *mut crate::leanh::LeanObject,
    mut v___y_1637_: *mut crate::leanh::LeanObject,
    mut v___y_1638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1639_ =
        l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1(
            v_00_u03b1_1630_,
            v_msg_1631_,
            v___y_1632_,
            v___y_1633_,
            v___y_1634_,
            v___y_1635_,
            v___y_1636_,
            v___y_1637_,
        );
    crate::leanh::lean_dec(v___y_1637_);
    crate::leanh::lean_dec_ref(v___y_1636_);
    crate::leanh::lean_dec(v___y_1635_);
    crate::leanh::lean_dec_ref(v___y_1634_);
    crate::leanh::lean_dec(v___y_1633_);
    crate::leanh::lean_dec_ref(v___y_1632_);
    return v_res_1639_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0(
    mut v_00_u03b1_1640_: *mut crate::leanh::LeanObject,
    mut v_stx_1641_: *mut crate::leanh::LeanObject,
    mut v_output_1642_: *mut crate::leanh::LeanObject,
    mut v_x_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
    mut v___y_1647_: *mut crate::leanh::LeanObject,
    mut v___y_1648_: *mut crate::leanh::LeanObject,
    mut v___y_1649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_stx_1641_, v_output_1642_, v_x_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___boxed(
    mut v_00_u03b1_1652_: *mut crate::leanh::LeanObject,
    mut v_stx_1653_: *mut crate::leanh::LeanObject,
    mut v_output_1654_: *mut crate::leanh::LeanObject,
    mut v_x_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1663_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0(v_00_u03b1_1652_, v_stx_1653_, v_output_1654_, v_x_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
    crate::leanh::lean_dec(v___y_1661_);
    crate::leanh::lean_dec_ref(v___y_1660_);
    crate::leanh::lean_dec(v___y_1659_);
    crate::leanh::lean_dec_ref(v___y_1658_);
    crate::leanh::lean_dec(v___y_1657_);
    crate::leanh::lean_dec_ref(v___y_1656_);
    return v_res_1663_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(
    mut v_msgData_1664_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(v_msgData_1664_, v_macroStack_1665_, v___y_1670_);
    return v___x_1673_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___boxed(
    mut v_msgData_1674_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
    mut v___y_1681_: *mut crate::leanh::LeanObject,
    mut v___y_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1683_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(v_msgData_1674_, v_macroStack_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
    crate::leanh::lean_dec(v___y_1681_);
    crate::leanh::lean_dec_ref(v___y_1680_);
    crate::leanh::lean_dec(v___y_1679_);
    crate::leanh::lean_dec_ref(v___y_1678_);
    crate::leanh::lean_dec(v___y_1677_);
    crate::leanh::lean_dec_ref(v___y_1676_);
    return v_res_1683_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4(
    mut v___y_1684_: *mut crate::leanh::LeanObject,
    mut v___y_1685_: *mut crate::leanh::LeanObject,
    mut v___y_1686_: *mut crate::leanh::LeanObject,
    mut v___y_1687_: *mut crate::leanh::LeanObject,
    mut v___y_1688_: *mut crate::leanh::LeanObject,
    mut v___y_1689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1691_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1689_);
    return v___x_1691_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v___y_1692_: *mut crate::leanh::LeanObject,
    mut v___y_1693_: *mut crate::leanh::LeanObject,
    mut v___y_1694_: *mut crate::leanh::LeanObject,
    mut v___y_1695_: *mut crate::leanh::LeanObject,
    mut v___y_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1699_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4(v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
    crate::leanh::lean_dec(v___y_1697_);
    crate::leanh::lean_dec_ref(v___y_1696_);
    crate::leanh::lean_dec(v___y_1695_);
    crate::leanh::lean_dec_ref(v___y_1694_);
    crate::leanh::lean_dec(v___y_1693_);
    crate::leanh::lean_dec_ref(v___y_1692_);
    return v_res_1699_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1700_: *mut crate::leanh::LeanObject,
    mut v_x_1701_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1702_: *mut crate::leanh::LeanObject,
    mut v___y_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: *mut crate::leanh::LeanObject,
    mut v___y_1705_: *mut crate::leanh::LeanObject,
    mut v___y_1706_: *mut crate::leanh::LeanObject,
    mut v___y_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(v_x_1701_, v_mkInfoTree_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
    return v___x_1710_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1711_: *mut crate::leanh::LeanObject,
    mut v_x_1712_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1713_: *mut crate::leanh::LeanObject,
    mut v___y_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1(v_00_u03b1_1711_, v_x_1712_, v_mkInfoTree_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
    crate::leanh::lean_dec(v___y_1719_);
    crate::leanh::lean_dec_ref(v___y_1718_);
    crate::leanh::lean_dec(v___y_1717_);
    crate::leanh::lean_dec_ref(v___y_1716_);
    crate::leanh::lean_dec(v___y_1715_);
    crate::leanh::lean_dec_ref(v___y_1714_);
    return v_res_1721_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_1758_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3;
    v___x_1759_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14;
    v___x_1760_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_1761_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1757_,
        v___x_1758_,
        v___x_1759_,
        v___x_1760_,
    );
    return v___x_1761_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___boxed(
    mut v_a_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1763_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1();
    return v_res_1763_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst(
    mut v_stx_1781_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_1782_: *mut crate::leanh::LeanObject,
    mut v_a_1783_: *mut crate::leanh::LeanObject,
    mut v_a_1784_: *mut crate::leanh::LeanObject,
    mut v_a_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
    mut v_a_1787_: *mut crate::leanh::LeanObject,
    mut v_a_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1790_ = lean_st_ref_get(v_a_1788_);
                v_env_1798_ = crate::leanh::lean_ctor_get(v___x_1790_, 0);
                crate::leanh::lean_inc_ref(v_env_1798_);
                crate::leanh::lean_dec(v___x_1790_);
                v___x_1799_ = l_Lake_dirExt;
                v_asyncMode_1800_ = crate::leanh::lean_ctor_get(v___x_1799_, 2);
                v___x_1801_ = crate::leanh::lean_box(0);
                v___x_1802_ = crate::leanh::lean_box(0);
                v___x_1803_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1801_,
                        v___x_1799_,
                        v_env_1798_,
                        v_asyncMode_1800_,
                        v___x_1802_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1803_) == 1 {
                    v_val_1804_ = crate::leanh::lean_ctor_get(v___x_1803_, 0);
                    crate::leanh::lean_inc(v_val_1804_);
                    crate::leanh::lean_dec_ref_known(v___x_1803_, 1);
                    v___x_1805_ = 0;
                    v___x_1806_ = l_Lean_SourceInfo_fromRef(v_stx_1781_, v___x_1805_);
                    v___x_1807_ = l_Lean_Syntax_mkStrLit(v_val_1804_, v___x_1806_);
                    v___x_1808_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3;
                    v___x_1809_ = l_Lean_mkCIdentFrom(v_stx_1781_, v___x_1808_, v___x_1805_);
                    v___x_1810_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1811_ = lean_mk_empty_array_with_capacity(v___x_1810_);
                    v___x_1812_ = lean_array_push(v___x_1811_, v___x_1807_);
                    v___x_1813_ = l_Lean_Syntax_mkApp(v___x_1809_, v___x_1812_);
                    v___y_1792_ = v___x_1813_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1803_);
                    v___x_1814_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5;
                    v___x_1815_ = 0;
                    v___x_1816_ = l_Lean_mkCIdentFrom(v_stx_1781_, v___x_1814_, v___x_1815_);
                    v___x_1817_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7;
                    v___x_1818_ = l_Lean_mkCIdentFrom(v_stx_1781_, v___x_1817_, v___x_1815_);
                    v___x_1819_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1820_ = lean_mk_empty_array_with_capacity(v___x_1819_);
                    v___x_1821_ = lean_array_push(v___x_1820_, v___x_1818_);
                    v___x_1822_ = l_Lean_Syntax_mkApp(v___x_1816_, v___x_1821_);
                    v___y_1792_ = v___x_1822_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1793_ = 1;
                v___x_1794_ = crate::leanh::lean_box((v___x_1793_) as usize);
                v___x_1795_ = crate::leanh::lean_box((v___x_1793_) as usize);
                crate::leanh::lean_inc(v___y_1792_);
                v___x_1796_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_elabTerm___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_1796_, 0, v___y_1792_);
                crate::leanh::lean_closure_set(v___x_1796_, 1, v_expectedType_x3f_1782_);
                crate::leanh::lean_closure_set(v___x_1796_, 2, v___x_1794_);
                crate::leanh::lean_closure_set(v___x_1796_, 3, v___x_1795_);
                v___x_1797_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_1781_, v___y_1792_, v___x_1796_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
                return v___x_1797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___boxed(
    mut v_stx_1823_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
    mut v_a_1827_: *mut crate::leanh::LeanObject,
    mut v_a_1828_: *mut crate::leanh::LeanObject,
    mut v_a_1829_: *mut crate::leanh::LeanObject,
    mut v_a_1830_: *mut crate::leanh::LeanObject,
    mut v_a_1831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1832_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst(
        v_stx_1823_,
        v_expectedType_x3f_1824_,
        v_a_1825_,
        v_a_1826_,
        v_a_1827_,
        v_a_1828_,
        v_a_1829_,
        v_a_1830_,
    );
    crate::leanh::lean_dec(v_a_1830_);
    crate::leanh::lean_dec_ref(v_a_1829_);
    crate::leanh::lean_dec(v_a_1828_);
    crate::leanh::lean_dec_ref(v_a_1827_);
    crate::leanh::lean_dec(v_a_1826_);
    crate::leanh::lean_dec_ref(v_a_1825_);
    return v_res_1832_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_1844_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1;
    v___x_1845_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3;
    v___x_1846_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_1847_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1843_,
        v___x_1844_,
        v___x_1845_,
        v___x_1846_,
    );
    return v___x_1847_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___boxed(
    mut v_a_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1849_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1();
    return v_res_1849_;
}
pub unsafe fn l_Lake_DSL_dummyGetConfig_x3f(
    mut v_a_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ = crate::leanh::lean_box(0);
    return v___x_1851_;
}
pub unsafe fn l_Lake_DSL_dummyGetConfig_x3f___boxed(
    mut v_a_1852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1853_ = l_Lake_DSL_dummyGetConfig_x3f(v_a_1852_);
    crate::leanh::lean_dec(v_a_1852_);
    return v_res_1853_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1854_ = crate::leanh::lean_box(0);
    v___x_1855_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1856_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1856_, 0, v___x_1855_);
    crate::leanh::lean_ctor_set(v___x_1856_, 1, v___x_1854_);
    return v___x_1856_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1858_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0);
    v___x_1859_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1859_, 0, v___x_1858_);
    return v___x_1859_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___boxed(
    mut v___y_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1861_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
    return v_res_1861_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0(
    mut v_00_u03b1_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
    return v___x_1870_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___boxed(
    mut v_00_u03b1_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
    mut v___y_1874_: *mut crate::leanh::LeanObject,
    mut v___y_1875_: *mut crate::leanh::LeanObject,
    mut v___y_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1879_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0(v_00_u03b1_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
    crate::leanh::lean_dec(v___y_1877_);
    crate::leanh::lean_dec_ref(v___y_1876_);
    crate::leanh::lean_dec(v___y_1875_);
    crate::leanh::lean_dec_ref(v___y_1874_);
    crate::leanh::lean_dec(v___y_1873_);
    crate::leanh::lean_dec_ref(v___y_1872_);
    return v_res_1879_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6;
    v___x_1895_ = l_String_toRawSubstring_x27(v___x_1894_);
    return v___x_1895_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Lake_DSL_dummyDir___closed__0;
    v___x_1928_ = l_String_toRawSubstring_x27(v___x_1927_);
    return v___x_1928_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1963_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36;
    v___x_1964_ = l_String_toRawSubstring_x27(v___x_1963_);
    return v___x_1964_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9;
    v___x_1978_ = l_String_toRawSubstring_x27(v___x_1977_);
    return v___x_1978_;
}
pub unsafe fn _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52;
    v___x_2002_ = l_String_toRawSubstring_x27(v___x_2001_);
    return v___x_2002_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig(
    mut v_stx_2030_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_2031_: *mut crate::leanh::LeanObject,
    mut v_a_2032_: *mut crate::leanh::LeanObject,
    mut v_a_2033_: *mut crate::leanh::LeanObject,
    mut v_a_2034_: *mut crate::leanh::LeanObject,
    mut v_a_2035_: *mut crate::leanh::LeanObject,
    mut v_a_2036_: *mut crate::leanh::LeanObject,
    mut v_a_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: u8 = 0;
    let mut v_a_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: u8 = 0;
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: u8 = 0;
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2148_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_expectedType_x3f_2031_);
                v___x_2039_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(
                    v_expectedType_x3f_2031_,
                    v_a_2032_,
                    v_a_2033_,
                    v_a_2034_,
                    v_a_2035_,
                    v_a_2036_,
                    v_a_2037_,
                );
                if crate::leanh::lean_obj_tag(v___x_2039_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2039_, 1);
                    v___x_2040_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1;
                    crate::leanh::lean_inc(v_stx_2030_);
                    v___x_2041_ = l_Lean_Syntax_isOfKind(v_stx_2030_, v___x_2040_);
                    if v___x_2041_ == 0 {
                        crate::leanh::lean_dec(v_expectedType_x3f_2031_);
                        crate::leanh::lean_dec(v_stx_2030_);
                        v___x_2048_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
                        return v___x_2048_;
                    } else {
                        v___x_2049_ = lean_st_ref_get(v_a_2037_);
                        v_env_2050_ = crate::leanh::lean_ctor_get(v___x_2049_, 0);
                        crate::leanh::lean_inc_ref(v_env_2050_);
                        crate::leanh::lean_dec(v___x_2049_);
                        v___x_2051_ = l_Lake_optsExt;
                        v_asyncMode_2052_ = crate::leanh::lean_ctor_get(v___x_2051_, 2);
                        v___x_2053_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2054_ = l_Lean_Syntax_getArg(v_stx_2030_, v___x_2053_);
                        v___x_2055_ = crate::leanh::lean_box(0);
                        v___x_2056_ = crate::leanh::lean_box(0);
                        v___x_2057_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2055_, v___x_2051_, v_env_2050_, v_asyncMode_2052_, v___x_2056_);
                        if crate::leanh::lean_obj_tag(v___x_2057_) == 1 {
                            v_val_2058_ = crate::leanh::lean_ctor_get(v___x_2057_, 0);
                            crate::leanh::lean_inc(v_val_2058_);
                            crate::leanh::lean_dec_ref_known(v___x_2057_, 1);
                            v___x_2059_ = l_Lean_TSyntax_getId(v___x_2054_);
                            crate::leanh::lean_dec(v___x_2054_);
                            v___x_2060_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_2058_, v___x_2059_);
                            crate::leanh::lean_dec(v___x_2059_);
                            crate::leanh::lean_dec(v_val_2058_);
                            if crate::leanh::lean_obj_tag(v___x_2060_) == 1 {
                                v_val_2061_ = crate::leanh::lean_ctor_get(v___x_2060_, 0);
                                crate::leanh::lean_inc(v_val_2061_);
                                crate::leanh::lean_dec_ref_known(v___x_2060_, 1);
                                v_ref_2062_ = crate::leanh::lean_ctor_get(v_a_2036_, 5);
                                v_quotContext_2063_ = crate::leanh::lean_ctor_get(v_a_2036_, 10);
                                v_currMacroScope_2064_ = crate::leanh::lean_ctor_get(v_a_2036_, 11);
                                v___x_2065_ = 0;
                                v___x_2066_ = l_Lean_SourceInfo_fromRef(v_ref_2062_, v___x_2065_);
                                v___x_2067_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5;
                                v___x_2068_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7), core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7_once), _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7);
                                v___x_2069_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8;
                                crate::leanh::lean_inc(v_currMacroScope_2064_);
                                crate::leanh::lean_inc(v_quotContext_2063_);
                                v___x_2070_ = l_Lean_addMacroScope(
                                    v_quotContext_2063_,
                                    v___x_2069_,
                                    v_currMacroScope_2064_,
                                );
                                v___x_2071_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12;
                                crate::leanh::lean_inc_n(v___x_2066_, 3);
                                v___x_2072_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2072_, 0, v___x_2066_);
                                crate::leanh::lean_ctor_set(v___x_2072_, 1, v___x_2068_);
                                crate::leanh::lean_ctor_set(v___x_2072_, 2, v___x_2070_);
                                crate::leanh::lean_ctor_set(v___x_2072_, 3, v___x_2071_);
                                v___x_2073_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14;
                                v___x_2074_ = l_Lean_Syntax_mkStrLit(v_val_2061_, v___x_2066_);
                                v___x_2075_ =
                                    l_Lean_Syntax_node1(v___x_2066_, v___x_2073_, v___x_2074_);
                                v___x_2076_ = l_Lean_Syntax_node2(
                                    v___x_2066_,
                                    v___x_2067_,
                                    v___x_2072_,
                                    v___x_2075_,
                                );
                                v_a_2043_ = v___x_2076_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2060_);
                                v_ref_2077_ = crate::leanh::lean_ctor_get(v_a_2036_, 5);
                                v_quotContext_2078_ = crate::leanh::lean_ctor_get(v_a_2036_, 10);
                                v_currMacroScope_2079_ = crate::leanh::lean_ctor_get(v_a_2036_, 11);
                                v___x_2080_ = 0;
                                v___x_2081_ = l_Lean_SourceInfo_fromRef(v_ref_2077_, v___x_2080_);
                                v___x_2082_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16;
                                v___x_2083_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18;
                                v___x_2084_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19;
                                crate::leanh::lean_inc_n(v___x_2081_, 12);
                                v___x_2085_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2085_, 0, v___x_2081_);
                                crate::leanh::lean_ctor_set(v___x_2085_, 1, v___x_2084_);
                                v___x_2086_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21;
                                v___x_2087_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22), core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22_once), _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22);
                                crate::leanh::lean_inc_n(v_currMacroScope_2079_, 4);
                                crate::leanh::lean_inc_n(v_quotContext_2078_, 4);
                                v___x_2088_ = l_Lean_addMacroScope(
                                    v_quotContext_2078_,
                                    v___x_2056_,
                                    v_currMacroScope_2079_,
                                );
                                v___x_2089_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35;
                                v___x_2090_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2090_, 0, v___x_2081_);
                                crate::leanh::lean_ctor_set(v___x_2090_, 1, v___x_2087_);
                                crate::leanh::lean_ctor_set(v___x_2090_, 2, v___x_2088_);
                                crate::leanh::lean_ctor_set(v___x_2090_, 3, v___x_2089_);
                                v___x_2091_ =
                                    l_Lean_Syntax_node1(v___x_2081_, v___x_2086_, v___x_2090_);
                                v___x_2092_ = l_Lean_Syntax_node2(
                                    v___x_2081_,
                                    v___x_2083_,
                                    v___x_2085_,
                                    v___x_2091_,
                                );
                                v___x_2093_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37), core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37_once), _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37);
                                v___x_2094_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38;
                                v___x_2095_ = l_Lean_addMacroScope(
                                    v_quotContext_2078_,
                                    v___x_2094_,
                                    v_currMacroScope_2079_,
                                );
                                v___x_2096_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41;
                                v___x_2097_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2097_, 0, v___x_2081_);
                                crate::leanh::lean_ctor_set(v___x_2097_, 1, v___x_2093_);
                                crate::leanh::lean_ctor_set(v___x_2097_, 2, v___x_2095_);
                                crate::leanh::lean_ctor_set(v___x_2097_, 3, v___x_2096_);
                                v___x_2098_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42;
                                v___x_2099_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2099_, 0, v___x_2081_);
                                crate::leanh::lean_ctor_set(v___x_2099_, 1, v___x_2098_);
                                v___x_2100_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14;
                                v___x_2101_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5;
                                v___x_2102_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43), core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43_once), _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43);
                                v___x_2103_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44;
                                v___x_2104_ = l_Lean_addMacroScope(
                                    v_quotContext_2078_,
                                    v___x_2103_,
                                    v_currMacroScope_2079_,
                                );
                                v___x_2105_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51;
                                v___x_2106_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2106_, 0, v___x_2081_);
                                crate::leanh::lean_ctor_set(v___x_2106_, 1, v___x_2102_);
                                crate::leanh::lean_ctor_set(v___x_2106_, 2, v___x_2104_);
                                crate::leanh::lean_ctor_set(v___x_2106_, 3, v___x_2105_);
                                v___x_2107_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53), core::ptr::addr_of_mut!(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53_once), _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53);
                                v___x_2108_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54;
                                v___x_2109_ = l_Lean_addMacroScope(
                                    v_quotContext_2078_,
                                    v___x_2108_,
                                    v_currMacroScope_2079_,
                                );
                                v___x_2110_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58;
                                v___x_2111_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2111_, 0, v___x_2081_);
                                crate::leanh::lean_ctor_set(v___x_2111_, 1, v___x_2107_);
                                crate::leanh::lean_ctor_set(v___x_2111_, 2, v___x_2109_);
                                crate::leanh::lean_ctor_set(v___x_2111_, 3, v___x_2110_);
                                v___x_2112_ =
                                    l_Lean_Syntax_node1(v___x_2081_, v___x_2100_, v___x_2111_);
                                v___x_2113_ = l_Lean_Syntax_node2(
                                    v___x_2081_,
                                    v___x_2101_,
                                    v___x_2106_,
                                    v___x_2112_,
                                );
                                v___x_2114_ =
                                    l_Lean_Syntax_node1(v___x_2081_, v___x_2100_, v___x_2113_);
                                v___x_2115_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59;
                                v___x_2116_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2116_, 0, v___x_2081_);
                                crate::leanh::lean_ctor_set(v___x_2116_, 1, v___x_2115_);
                                v___x_2117_ = l_Lean_Syntax_node5(
                                    v___x_2081_,
                                    v___x_2082_,
                                    v___x_2092_,
                                    v___x_2097_,
                                    v___x_2099_,
                                    v___x_2114_,
                                    v___x_2116_,
                                );
                                v_a_2043_ = v___x_2117_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2057_);
                            v___x_2118_ =
                                l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61;
                            v___x_2119_ = 0;
                            v___x_2120_ =
                                l_Lean_mkCIdentFrom(v_stx_2030_, v___x_2118_, v___x_2119_);
                            v___x_2126_ = l_Lean_TSyntax_getId(v___x_2054_);
                            crate::leanh::lean_dec(v___x_2054_);
                            v___x_2127_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___x_2126_);
                            v___x_2128_ =
                                l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                    v___x_2127_,
                                    v___x_2126_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_2128_) == 0 {
                                v___x_2129_ = l_Lean_quoteNameMk(v___x_2126_);
                                v___y_2122_ = v___x_2129_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2126_);
                                v_val_2130_ = crate::leanh::lean_ctor_get(v___x_2128_, 0);
                                crate::leanh::lean_inc(v_val_2130_);
                                crate::leanh::lean_dec_ref_known(v___x_2128_, 1);
                                v___x_2131_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63;
                                v___x_2132_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64;
                                v___x_2133_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65;
                                v___x_2134_ = lean_string_intercalate(v___x_2133_, v_val_2130_);
                                v___x_2135_ = lean_string_append(v___x_2132_, v___x_2134_);
                                crate::leanh::lean_dec_ref(v___x_2134_);
                                v___x_2136_ = crate::leanh::lean_box(2);
                                v___x_2137_ = l_Lean_Syntax_mkNameLit(v___x_2135_, v___x_2136_);
                                v___x_2138_ = lean_mk_empty_array_with_capacity(v___x_2053_);
                                v___x_2139_ = lean_array_push(v___x_2138_, v___x_2137_);
                                v___x_2140_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2140_, 0, v___x_2136_);
                                crate::leanh::lean_ctor_set(v___x_2140_, 1, v___x_2131_);
                                crate::leanh::lean_ctor_set(v___x_2140_, 2, v___x_2139_);
                                v___y_2122_ = v___x_2140_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_expectedType_x3f_2031_);
                    crate::leanh::lean_dec(v_stx_2030_);
                    v_a_2141_ = crate::leanh::lean_ctor_get(v___x_2039_, 0);
                    v_isSharedCheck_2148_ = (!crate::leanh::lean_is_exclusive(v___x_2039_)) as u8;
                    if v_isSharedCheck_2148_ == 0 {
                        v___x_2143_ = v___x_2039_;
                        v_isShared_2144_ = v_isSharedCheck_2148_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2141_);
                        crate::leanh::lean_dec(v___x_2039_);
                        v___x_2143_ = crate::leanh::lean_box(0);
                        v_isShared_2144_ = v_isSharedCheck_2148_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2044_ = crate::leanh::lean_box((v___x_2041_) as usize);
                v___x_2045_ = crate::leanh::lean_box((v___x_2041_) as usize);
                crate::leanh::lean_inc(v_a_2043_);
                v___x_2046_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_elabTerm___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_2046_, 0, v_a_2043_);
                crate::leanh::lean_closure_set(v___x_2046_, 1, v_expectedType_x3f_2031_);
                crate::leanh::lean_closure_set(v___x_2046_, 2, v___x_2044_);
                crate::leanh::lean_closure_set(v___x_2046_, 3, v___x_2045_);
                v___x_2047_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_2030_, v_a_2043_, v___x_2046_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
                return v___x_2047_;
            }
            2 => {
                v___x_2123_ = lean_mk_empty_array_with_capacity(v___x_2053_);
                v___x_2124_ = lean_array_push(v___x_2123_, v___y_2122_);
                v___x_2125_ = l_Lean_Syntax_mkApp(v___x_2120_, v___x_2124_);
                v_a_2043_ = v___x_2125_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_2144_ == 0 {
                    v___x_2146_ = v___x_2143_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
                    v___x_2146_ = v_reuseFailAlloc_2147_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2146_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___boxed(
    mut v_stx_2149_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_2150_: *mut crate::leanh::LeanObject,
    mut v_a_2151_: *mut crate::leanh::LeanObject,
    mut v_a_2152_: *mut crate::leanh::LeanObject,
    mut v_a_2153_: *mut crate::leanh::LeanObject,
    mut v_a_2154_: *mut crate::leanh::LeanObject,
    mut v_a_2155_: *mut crate::leanh::LeanObject,
    mut v_a_2156_: *mut crate::leanh::LeanObject,
    mut v_a_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2158_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig(
        v_stx_2149_,
        v_expectedType_x3f_2150_,
        v_a_2151_,
        v_a_2152_,
        v_a_2153_,
        v_a_2154_,
        v_a_2155_,
        v_a_2156_,
    );
    crate::leanh::lean_dec(v_a_2156_);
    crate::leanh::lean_dec_ref(v_a_2155_);
    crate::leanh::lean_dec(v_a_2154_);
    crate::leanh::lean_dec_ref(v_a_2153_);
    crate::leanh::lean_dec(v_a_2152_);
    crate::leanh::lean_dec_ref(v_a_2151_);
    return v_res_2158_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2164_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_2165_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1;
    v___x_2166_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1;
    v___x_2167_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2168_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2164_,
        v___x_2165_,
        v___x_2166_,
        v___x_2167_,
    );
    return v___x_2168_;
}
pub unsafe fn l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___boxed(
    mut v_a_2169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2170_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1();
    return v_res_2170_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Config(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Extensions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Config(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Config(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_DSL_Extensions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_DSL_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_Config(builtin);
}
