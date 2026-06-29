// Lean compiler output
// Module: Lake.DSL.Meta
// Imports: Lean.ToExpr Lean.Elab.Eval Lake.DSL.Syntax
use crate::ffi::{
    lean_array_push, lean_get_set_stderr, lean_get_set_stdin, lean_get_set_stdout,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_panic_fn_borrowed, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq,
    lean_string_from_utf8_unchecked, lean_string_utf8_byte_size, lean_string_validate_utf8,
};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_ByteArray_empty, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IO::l_IO_FS_Stream_ofBuffer;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::DSL::Syntax::{
    initialize_Lake_DSL_Syntax, runtime_initialize_Lake_DSL_Syntax,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_commandElabAttribute, l_Lean_Elab_Command_elabCommand___boxed,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_runTermElabM___redArg,
    l_Lean_Elab_Command_withMacroExpansion___redArg,
};
use crate::r#gen::Lean::Elab::Eval::{
    initialize_Lean_Elab_Eval, l_Lean_Elab_Term_evalTerm___redArg,
    runtime_initialize_Lean_Elab_Eval,
};
use crate::r#gen::Lean::Elab::Exception::{
    l_Lean_Elab_abortTermExceptionId, l_Lean_Elab_unsupportedSyntaxExceptionId,
};
use crate::r#gen::Lean::Elab::SyntheticMVars::l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTermEnsuringType, l_Lean_Elab_Term_logUnassignedUsingErrorInfos,
    l_Lean_Elab_Term_termElabAttribute,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_hasMVar, l_Lean_mkConst, l_Lean_mkSort,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Level::l_Lean_Level_succ___override;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkAppM;
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_mkFreshExprMVar;
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::Meta::Eval::l_Lean_Meta_evalExpr___redArg;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::ToExpr::{initialize_Lean_ToExpr, runtime_initialize_Lean_ToExpr};
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value:
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
    m_data: [76, 97, 107, 101, 0],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value:
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
    m_data: [68, 83, 76, 0],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__2_value:
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
    m_data: [99, 109, 100, 68, 111, 0],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3_value_aux_1:
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
            l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5901868804703194544 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3_value:
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
            l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__2_value)
            as *mut crate::leanh::LeanObject,
        4812447225742894945 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__4_value:
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
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__5_value:
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
    m_data: [103, 114, 111, 117, 112, 0],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__6_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__5_value)
            as *mut crate::leanh::LeanObject,
        2214559063752339918 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__0_value:
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
    m_data: [66, 111, 111, 108, 0],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__1_value:
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
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        12882480457794858234 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__0_value:
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
    m_data: [109, 101, 116, 97, 73, 102, 0],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1_value_aux_1:
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
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5901868804703194544 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1_value:
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
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14561490878273970730 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__2_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 109, 101, 116, 97, 32, 105, 102, 32,
        99, 111, 109, 109, 97, 110, 100, 0,
    ],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__4_value:
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
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__5_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__4_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__0_value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value) as *mut crate::leanh::LeanObject,12997130533650095963 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value) as *mut crate::leanh::LeanObject,11286550318989764116 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__4_value) as *mut crate::leanh::LeanObject,10109521560113520776 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__5_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,15101942887191573217 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value) as *mut crate::leanh::LeanObject,14879603394420122717 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value) as *mut crate::leanh::LeanObject,14500103005319432682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__9_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 77, 101, 116, 97, 73, 102, 0]};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__9_value) as *mut crate::leanh::LeanObject,5820656222658071689 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__0_value:
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
    m_data: [73, 79, 0],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__1_value:
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
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        4390522573605260290 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__3_value:
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
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__4_value:
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
    m_data: [69, 120, 112, 114, 0],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__4_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5_value_aux_0:
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
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5_value:
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
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        5933584171502587988 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__1_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 66, 97, 115, 105, 99, 0]};
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__2_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 116, 114, 105, 110, 103, 46, 102, 114, 111, 109, 85, 84, 70, 56, 33, 0]};
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__3_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__0_value:
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
    m_data: [114, 117, 110, 73, 79, 0],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5901868804703194544 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__0_value)
            as *mut crate::leanh::LeanObject,
        891786894088060352 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5_value:
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
    m_data: [116, 111, 69, 120, 112, 114, 73, 79, 0],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5901868804703194544 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5_value)
            as *mut crate::leanh::LeanObject,
        11934663079361438308 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__7_value:
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
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value:
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
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9_value:
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
    m_data: [100, 111, 0],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_0:
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
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_1:
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
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__7_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_2:
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
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value:
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
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9_value)
            as *mut crate::leanh::LeanObject,
        5817315006727311029 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 82, 117, 110, 73, 79, 0]};
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__0_value) as *mut crate::leanh::LeanObject,9676963476092644130 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo(
    mut v_x_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    v___x_1654_ = l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3;
    crate::leanh::lean_inc(v_x_1653_);
    v___x_1655_ = l_Lean_Syntax_isOfKind(v_x_1653_, v___x_1654_);
    if v___x_1655_ == 0 {
        let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1653_);
        v___x_1656_ = l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__4;
        return v___x_1656_;
    } else {
        let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_cmd_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1660_: u8 = 0;
        v___x_1657_ = crate::leanh::lean_unsigned_to_nat(0);
        v_cmd_1658_ = l_Lean_Syntax_getArg(v_x_1653_, v___x_1657_);
        crate::leanh::lean_dec(v_x_1653_);
        v___x_1659_ = l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__6;
        crate::leanh::lean_inc(v_cmd_1658_);
        v___x_1660_ = l_Lean_Syntax_isOfKind(v_cmd_1658_, v___x_1659_);
        if v___x_1660_ == 0 {
            let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1661_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1662_ = lean_mk_empty_array_with_capacity(v___x_1661_);
            v___x_1663_ = lean_array_push(v___x_1662_, v_cmd_1658_);
            return v___x_1663_;
        } else {
            let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1664_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1665_ = l_Lean_Syntax_getArg(v_cmd_1658_, v___x_1664_);
            crate::leanh::lean_dec(v_cmd_1658_);
            v___x_1666_ = l_Lean_Syntax_getArgs(v___x_1665_);
            crate::leanh::lean_dec(v___x_1665_);
            return v___x_1666_;
        }
    }
}
pub unsafe fn _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1670_ = crate::leanh::lean_box(0);
    v___x_1671_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__1;
    v___x_1672_ = l_Lean_mkConst(v___x_1671_, v___x_1670_);
    return v___x_1672_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1(
    mut v_c_1673_: *mut crate::leanh::LeanObject,
    mut v_a_1674_: *mut crate::leanh::LeanObject,
    mut v_a_1675_: *mut crate::leanh::LeanObject,
    mut v_a_1676_: *mut crate::leanh::LeanObject,
    mut v_a_1677_: *mut crate::leanh::LeanObject,
    mut v_a_1678_: *mut crate::leanh::LeanObject,
    mut v_a_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: u8 = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2_once
        ),
        _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2,
    );
    v___x_1682_ = 0;
    v___x_1683_ = l_Lean_Elab_Term_evalTerm___redArg(
        v___x_1681_,
        v_c_1673_,
        v___x_1682_,
        v_a_1674_,
        v_a_1675_,
        v_a_1676_,
        v_a_1677_,
        v_a_1678_,
        v_a_1679_,
    );
    return v___x_1683_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___boxed(
    mut v_c_1684_: *mut crate::leanh::LeanObject,
    mut v_a_1685_: *mut crate::leanh::LeanObject,
    mut v_a_1686_: *mut crate::leanh::LeanObject,
    mut v_a_1687_: *mut crate::leanh::LeanObject,
    mut v_a_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1(
        v_c_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_,
    );
    crate::leanh::lean_dec(v_a_1690_);
    crate::leanh::lean_dec_ref(v_a_1689_);
    crate::leanh::lean_dec(v_a_1688_);
    crate::leanh::lean_dec_ref(v_a_1687_);
    crate::leanh::lean_dec(v_a_1686_);
    crate::leanh::lean_dec_ref(v_a_1685_);
    return v_res_1692_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0(
    mut v_c_1693_: *mut crate::leanh::LeanObject,
    mut v_x_1694_: *mut crate::leanh::LeanObject,
    mut v___y_1695_: *mut crate::leanh::LeanObject,
    mut v___y_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1(
        v_c_1693_,
        v___y_1695_,
        v___y_1696_,
        v___y_1697_,
        v___y_1698_,
        v___y_1699_,
        v___y_1700_,
    );
    return v___x_1702_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0___boxed(
    mut v_c_1703_: *mut crate::leanh::LeanObject,
    mut v_x_1704_: *mut crate::leanh::LeanObject,
    mut v___y_1705_: *mut crate::leanh::LeanObject,
    mut v___y_1706_: *mut crate::leanh::LeanObject,
    mut v___y_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
    mut v___y_1710_: *mut crate::leanh::LeanObject,
    mut v___y_1711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0(
        v_c_1703_,
        v_x_1704_,
        v___y_1705_,
        v___y_1706_,
        v___y_1707_,
        v___y_1708_,
        v___y_1709_,
        v___y_1710_,
    );
    crate::leanh::lean_dec(v___y_1710_);
    crate::leanh::lean_dec_ref(v___y_1709_);
    crate::leanh::lean_dec(v___y_1708_);
    crate::leanh::lean_dec_ref(v___y_1707_);
    crate::leanh::lean_dec(v___y_1706_);
    crate::leanh::lean_dec_ref(v___y_1705_);
    crate::leanh::lean_dec_ref(v_x_1704_);
    return v_res_1712_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1713_ = crate::leanh::lean_box(1);
    v___x_1714_ = l_Lean_MessageData_ofFormat(v___x_1713_);
    return v___x_1714_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1718_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__2;
    v___x_1719_ = l_Lean_MessageData_ofFormat(v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4(
    mut v_x_1720_: *mut crate::leanh::LeanObject,
    mut v_x_1721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1726_: u8 = 0;
    let mut v_before_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut v_unused_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1721_) == 0 {
                    return v_x_1720_;
                } else {
                    v_head_1722_ = crate::leanh::lean_ctor_get(v_x_1721_, 0);
                    v_tail_1723_ = crate::leanh::lean_ctor_get(v_x_1721_, 1);
                    v_isSharedCheck_1745_ = (!crate::leanh::lean_is_exclusive(v_x_1721_)) as u8;
                    if v_isSharedCheck_1745_ == 0 {
                        v___x_1725_ = v_x_1721_;
                        v_isShared_1726_ = v_isSharedCheck_1745_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1723_);
                        crate::leanh::lean_inc(v_head_1722_);
                        crate::leanh::lean_dec(v_x_1721_);
                        v___x_1725_ = crate::leanh::lean_box(0);
                        v_isShared_1726_ = v_isSharedCheck_1745_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1727_ = crate::leanh::lean_ctor_get(v_head_1722_, 0);
                v_isSharedCheck_1743_ = (!crate::leanh::lean_is_exclusive(v_head_1722_)) as u8;
                if v_isSharedCheck_1743_ == 0 {
                    v_unused_1744_ = crate::leanh::lean_ctor_get(v_head_1722_, 1);
                    crate::leanh::lean_dec(v_unused_1744_);
                    v___x_1729_ = v_head_1722_;
                    v_isShared_1730_ = v_isSharedCheck_1743_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_1727_);
                    crate::leanh::lean_dec(v_head_1722_);
                    v___x_1729_ = crate::leanh::lean_box(0);
                    v_isShared_1730_ = v_isSharedCheck_1743_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1731_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0);
                if v_isShared_1730_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1729_, 7);
                    crate::leanh::lean_ctor_set(v___x_1729_, 1, v___x_1731_);
                    crate::leanh::lean_ctor_set(v___x_1729_, 0, v_x_1720_);
                    v___x_1733_ = v___x_1729_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_x_1720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___x_1731_);
                    v___x_1733_ = v_reuseFailAlloc_1742_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1734_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3);
                if v_isShared_1726_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1725_, 7);
                    crate::leanh::lean_ctor_set(v___x_1725_, 1, v___x_1734_);
                    crate::leanh::lean_ctor_set(v___x_1725_, 0, v___x_1733_);
                    v___x_1736_ = v___x_1725_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1741_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 1, v___x_1734_);
                    v___x_1736_ = v_reuseFailAlloc_1741_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1737_ = l_Lean_MessageData_ofSyntax(v_before_1727_);
                v___x_1738_ = l_Lean_indentD(v___x_1737_);
                v___x_1739_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1739_, 0, v___x_1736_);
                crate::leanh::lean_ctor_set(v___x_1739_, 1, v___x_1738_);
                v_x_1720_ = v___x_1739_;
                v_x_1721_ = v_tail_1723_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(
    mut v_opts_1746_: *mut crate::leanh::LeanObject,
    mut v_opt_1747_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1748_ = crate::leanh::lean_ctor_get(v_opt_1747_, 0);
    v_defValue_1749_ = crate::leanh::lean_ctor_get(v_opt_1747_, 1);
    v_map_1750_ = crate::leanh::lean_ctor_get(v_opts_1746_, 0);
    v___x_1751_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1750_,
            v_name_1748_,
        );
    if crate::leanh::lean_obj_tag(v___x_1751_) == 0 {
        let mut v___x_1752_: u8 = 0;
        v___x_1752_ = (crate::leanh::lean_unbox(v_defValue_1749_) as u8);
        return v___x_1752_;
    } else {
        let mut v_val_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1753_ = crate::leanh::lean_ctor_get(v___x_1751_, 0);
        crate::leanh::lean_inc(v_val_1753_);
        crate::leanh::lean_dec_ref_known(v___x_1751_, 1);
        if crate::leanh::lean_obj_tag(v_val_1753_) == 1 {
            let mut v_v_1754_: u8 = 0;
            v_v_1754_ = crate::leanh::lean_ctor_get_uint8(v_val_1753_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1753_, 0);
            return v_v_1754_;
        } else {
            let mut v___x_1755_: u8 = 0;
            crate::leanh::lean_dec(v_val_1753_);
            v___x_1755_ = (crate::leanh::lean_unbox(v_defValue_1749_) as u8);
            return v___x_1755_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_opts_1756_: *mut crate::leanh::LeanObject,
    mut v_opt_1757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1758_: u8 = 0;
    let mut v_r_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1758_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v_opts_1756_, v_opt_1757_);
    crate::leanh::lean_dec_ref(v_opt_1757_);
    crate::leanh::lean_dec_ref(v_opts_1756_);
    v_r_1759_ = crate::leanh::lean_box((v_res_1758_) as usize);
    return v_r_1759_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__1;
    v___x_1764_ = l_Lean_MessageData_ofFormat(v___x_1763_);
    return v___x_1764_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(
    mut v_msgData_1765_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1766_: *mut crate::leanh::LeanObject,
    mut v___y_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: u8 = 0;
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1782_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1794_: u8 = 0;
    let mut v_unused_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1769_ = lean_st_ref_get(v___y_1767_);
                v_scopes_1770_ = crate::leanh::lean_ctor_get(v___x_1769_, 2);
                crate::leanh::lean_inc(v_scopes_1770_);
                crate::leanh::lean_dec(v___x_1769_);
                v___x_1771_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_1772_ = l_List_head_x21___redArg(v___x_1771_, v_scopes_1770_);
                crate::leanh::lean_dec(v_scopes_1770_);
                v_opts_1773_ = crate::leanh::lean_ctor_get(v___x_1772_, 1);
                crate::leanh::lean_inc_ref(v_opts_1773_);
                crate::leanh::lean_dec(v___x_1772_);
                v___x_1774_ = l_Lean_Elab_pp_macroStack;
                v___x_1775_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v_opts_1773_, v___x_1774_);
                crate::leanh::lean_dec_ref(v_opts_1773_);
                if v___x_1775_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_1766_);
                    v___x_1776_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1776_, 0, v_msgData_1765_);
                    return v___x_1776_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_1766_) == 0 {
                        v___x_1777_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1777_, 0, v_msgData_1765_);
                        return v___x_1777_;
                    } else {
                        v_head_1778_ = crate::leanh::lean_ctor_get(v_macroStack_1766_, 0);
                        crate::leanh::lean_inc(v_head_1778_);
                        v_after_1779_ = crate::leanh::lean_ctor_get(v_head_1778_, 1);
                        v_isSharedCheck_1794_ =
                            (!crate::leanh::lean_is_exclusive(v_head_1778_)) as u8;
                        if v_isSharedCheck_1794_ == 0 {
                            v_unused_1795_ = crate::leanh::lean_ctor_get(v_head_1778_, 0);
                            crate::leanh::lean_dec(v_unused_1795_);
                            v___x_1781_ = v_head_1778_;
                            v_isShared_1782_ = v_isSharedCheck_1794_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_1779_);
                            crate::leanh::lean_dec(v_head_1778_);
                            v___x_1781_ = crate::leanh::lean_box(0);
                            v_isShared_1782_ = v_isSharedCheck_1794_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1783_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0);
                if v_isShared_1782_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1781_, 7);
                    crate::leanh::lean_ctor_set(v___x_1781_, 1, v___x_1783_);
                    crate::leanh::lean_ctor_set(v___x_1781_, 0, v_msgData_1765_);
                    v___x_1785_ = v___x_1781_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_msgData_1765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___x_1783_);
                    v___x_1785_ = v_reuseFailAlloc_1793_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1786_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2);
                v___x_1787_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1787_, 0, v___x_1785_);
                crate::leanh::lean_ctor_set(v___x_1787_, 1, v___x_1786_);
                v___x_1788_ = l_Lean_MessageData_ofSyntax(v_after_1779_);
                v___x_1789_ = l_Lean_indentD(v___x_1788_);
                v_msgData_1790_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_1790_, 0, v___x_1787_);
                crate::leanh::lean_ctor_set(v_msgData_1790_, 1, v___x_1789_);
                v___x_1791_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4(v_msgData_1790_, v_macroStack_1766_);
                v___x_1792_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1792_, 0, v___x_1791_);
                return v___x_1792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_msgData_1796_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1797_: *mut crate::leanh::LeanObject,
    mut v___y_1798_: *mut crate::leanh::LeanObject,
    mut v___y_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1800_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(v_msgData_1796_, v_macroStack_1797_, v___y_1798_);
    crate::leanh::lean_dec(v___y_1798_);
    return v_res_1800_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1801_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1801_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1802_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_1803_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1803_, 0, v___x_1802_);
    return v___x_1803_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1804_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1805_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1806_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1806_, 0, v___x_1805_);
    crate::leanh::lean_ctor_set(v___x_1806_, 1, v___x_1805_);
    crate::leanh::lean_ctor_set(v___x_1806_, 2, v___x_1805_);
    crate::leanh::lean_ctor_set(v___x_1806_, 3, v___x_1805_);
    crate::leanh::lean_ctor_set(v___x_1806_, 4, v___x_1804_);
    crate::leanh::lean_ctor_set(v___x_1806_, 5, v___x_1804_);
    crate::leanh::lean_ctor_set(v___x_1806_, 6, v___x_1804_);
    crate::leanh::lean_ctor_set(v___x_1806_, 7, v___x_1804_);
    crate::leanh::lean_ctor_set(v___x_1806_, 8, v___x_1804_);
    crate::leanh::lean_ctor_set(v___x_1806_, 9, v___x_1804_);
    return v___x_1806_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1807_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1808_ = lean_mk_empty_array_with_capacity(v___x_1807_);
    v___x_1809_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1809_, 0, v___x_1808_);
    return v___x_1809_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1810_: usize = 0;
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = 5usize;
    v___x_1811_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1812_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1813_ = lean_mk_empty_array_with_capacity(v___x_1812_);
    v___x_1814_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1815_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1815_, 0, v___x_1814_);
    crate::leanh::lean_ctor_set(v___x_1815_, 1, v___x_1813_);
    crate::leanh::lean_ctor_set(v___x_1815_, 2, v___x_1811_);
    crate::leanh::lean_ctor_set(v___x_1815_, 3, v___x_1811_);
    crate::leanh::lean_ctor_set_usize(v___x_1815_, 4, v___x_1810_);
    return v___x_1815_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1816_ = crate::leanh::lean_box(1);
    v___x_1817_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4);
    v___x_1818_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1819_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1819_, 0, v___x_1818_);
    crate::leanh::lean_ctor_set(v___x_1819_, 1, v___x_1817_);
    crate::leanh::lean_ctor_set(v___x_1819_, 2, v___x_1816_);
    return v___x_1819_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(
    mut v_msgData_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1823_ = lean_st_ref_get(v___y_1821_);
    v_env_1824_ = crate::leanh::lean_ctor_get(v___x_1823_, 0);
    crate::leanh::lean_inc_ref(v_env_1824_);
    crate::leanh::lean_dec(v___x_1823_);
    v___x_1825_ = lean_st_ref_get(v___y_1821_);
    v_scopes_1826_ = crate::leanh::lean_ctor_get(v___x_1825_, 2);
    crate::leanh::lean_inc(v_scopes_1826_);
    crate::leanh::lean_dec(v___x_1825_);
    v___x_1827_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1828_ = l_List_head_x21___redArg(v___x_1827_, v_scopes_1826_);
    crate::leanh::lean_dec(v_scopes_1826_);
    v_opts_1829_ = crate::leanh::lean_ctor_get(v___x_1828_, 1);
    crate::leanh::lean_inc_ref(v_opts_1829_);
    crate::leanh::lean_dec(v___x_1828_);
    v___x_1830_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2);
    v___x_1831_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5);
    v___x_1832_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1832_, 0, v_env_1824_);
    crate::leanh::lean_ctor_set(v___x_1832_, 1, v___x_1830_);
    crate::leanh::lean_ctor_set(v___x_1832_, 2, v___x_1831_);
    crate::leanh::lean_ctor_set(v___x_1832_, 3, v_opts_1829_);
    v___x_1833_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1833_, 0, v___x_1832_);
    crate::leanh::lean_ctor_set(v___x_1833_, 1, v_msgData_1820_);
    v___x_1834_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1834_, 0, v___x_1833_);
    return v___x_1834_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msgData_1835_: *mut crate::leanh::LeanObject,
    mut v___y_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1838_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(v_msgData_1835_, v___y_1836_);
    crate::leanh::lean_dec(v___y_1836_);
    return v_res_1838_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(
    mut v_msg_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut v_a_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1843_ = l_Lean_Elab_Command_getRef___redArg(v___y_1840_);
                if crate::leanh::lean_obj_tag(v___x_1843_) == 0 {
                    v_a_1844_ = crate::leanh::lean_ctor_get(v___x_1843_, 0);
                    crate::leanh::lean_inc(v_a_1844_);
                    crate::leanh::lean_dec_ref_known(v___x_1843_, 1);
                    v_macroStack_1845_ = crate::leanh::lean_ctor_get(v___y_1840_, 4);
                    v___x_1846_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(v_msg_1839_, v___y_1841_);
                    v_a_1847_ = crate::leanh::lean_ctor_get(v___x_1846_, 0);
                    crate::leanh::lean_inc(v_a_1847_);
                    crate::leanh::lean_dec_ref(v___x_1846_);
                    v___x_1848_ = l_Lean_Elab_getBetterRef(v_a_1844_, v_macroStack_1845_);
                    crate::leanh::lean_dec(v_a_1844_);
                    crate::leanh::lean_inc(v_macroStack_1845_);
                    v___x_1849_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(v_a_1847_, v_macroStack_1845_, v___y_1841_);
                    v_a_1850_ = crate::leanh::lean_ctor_get(v___x_1849_, 0);
                    v_isSharedCheck_1858_ = (!crate::leanh::lean_is_exclusive(v___x_1849_)) as u8;
                    if v_isSharedCheck_1858_ == 0 {
                        v___x_1852_ = v___x_1849_;
                        v_isShared_1853_ = v_isSharedCheck_1858_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1850_);
                        crate::leanh::lean_dec(v___x_1849_);
                        v___x_1852_ = crate::leanh::lean_box(0);
                        v_isShared_1853_ = v_isSharedCheck_1858_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_1839_);
                    v_a_1859_ = crate::leanh::lean_ctor_get(v___x_1843_, 0);
                    v_isSharedCheck_1866_ = (!crate::leanh::lean_is_exclusive(v___x_1843_)) as u8;
                    if v_isSharedCheck_1866_ == 0 {
                        v___x_1861_ = v___x_1843_;
                        v_isShared_1862_ = v_isSharedCheck_1866_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1859_);
                        crate::leanh::lean_dec(v___x_1843_);
                        v___x_1861_ = crate::leanh::lean_box(0);
                        v_isShared_1862_ = v_isSharedCheck_1866_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1854_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1854_, 0, v___x_1848_);
                crate::leanh::lean_ctor_set(v___x_1854_, 1, v_a_1850_);
                if v_isShared_1853_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1852_, 1);
                    crate::leanh::lean_ctor_set(v___x_1852_, 0, v___x_1854_);
                    v___x_1856_ = v___x_1852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
                    v___x_1856_ = v_reuseFailAlloc_1857_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1856_;
            }
            3 => {
                if v_isShared_1862_ == 0 {
                    v___x_1864_ = v___x_1861_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1865_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
                    v___x_1864_ = v_reuseFailAlloc_1865_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1864_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg___boxed(
    mut v_msg_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
    mut v___y_1869_: *mut crate::leanh::LeanObject,
    mut v___y_1870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1871_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(v_msg_1867_, v___y_1868_, v___y_1869_);
    crate::leanh::lean_dec(v___y_1869_);
    crate::leanh::lean_dec_ref(v___y_1868_);
    return v_res_1871_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(
    mut v_ref_1872_: *mut crate::leanh::LeanObject,
    mut v_msg_1873_: *mut crate::leanh::LeanObject,
    mut v___y_1874_: *mut crate::leanh::LeanObject,
    mut v___y_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1888_: u8 = 0;
    let mut v_ref_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1899_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1877_ = l_Lean_Elab_Command_getRef___redArg(v___y_1874_);
                if crate::leanh::lean_obj_tag(v___x_1877_) == 0 {
                    v_a_1878_ = crate::leanh::lean_ctor_get(v___x_1877_, 0);
                    crate::leanh::lean_inc(v_a_1878_);
                    crate::leanh::lean_dec_ref_known(v___x_1877_, 1);
                    v_fileName_1879_ = crate::leanh::lean_ctor_get(v___y_1874_, 0);
                    v_fileMap_1880_ = crate::leanh::lean_ctor_get(v___y_1874_, 1);
                    v_currRecDepth_1881_ = crate::leanh::lean_ctor_get(v___y_1874_, 2);
                    v_cmdPos_1882_ = crate::leanh::lean_ctor_get(v___y_1874_, 3);
                    v_macroStack_1883_ = crate::leanh::lean_ctor_get(v___y_1874_, 4);
                    v_quotContext_x3f_1884_ = crate::leanh::lean_ctor_get(v___y_1874_, 5);
                    v_currMacroScope_1885_ = crate::leanh::lean_ctor_get(v___y_1874_, 6);
                    v_snap_x3f_1886_ = crate::leanh::lean_ctor_get(v___y_1874_, 8);
                    v_cancelTk_x3f_1887_ = crate::leanh::lean_ctor_get(v___y_1874_, 9);
                    v_suppressElabErrors_1888_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1874_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_1889_ = l_Lean_replaceRef(v_ref_1872_, v_a_1878_);
                    crate::leanh::lean_dec(v_a_1878_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_1887_);
                    crate::leanh::lean_inc(v_snap_x3f_1886_);
                    crate::leanh::lean_inc(v_currMacroScope_1885_);
                    crate::leanh::lean_inc(v_quotContext_x3f_1884_);
                    crate::leanh::lean_inc(v_macroStack_1883_);
                    crate::leanh::lean_inc(v_cmdPos_1882_);
                    crate::leanh::lean_inc(v_currRecDepth_1881_);
                    crate::leanh::lean_inc_ref(v_fileMap_1880_);
                    crate::leanh::lean_inc_ref(v_fileName_1879_);
                    v___x_1890_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1890_, 0, v_fileName_1879_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 1, v_fileMap_1880_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 2, v_currRecDepth_1881_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 3, v_cmdPos_1882_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 4, v_macroStack_1883_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 5, v_quotContext_x3f_1884_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 6, v_currMacroScope_1885_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 7, v_ref_1889_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 8, v_snap_x3f_1886_);
                    crate::leanh::lean_ctor_set(v___x_1890_, 9, v_cancelTk_x3f_1887_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1890_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_1888_,
                    );
                    v___x_1891_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(v_msg_1873_, v___x_1890_, v___y_1875_);
                    crate::leanh::lean_dec_ref_known(v___x_1890_, 10);
                    return v___x_1891_;
                } else {
                    crate::leanh::lean_dec_ref(v_msg_1873_);
                    v_a_1892_ = crate::leanh::lean_ctor_get(v___x_1877_, 0);
                    v_isSharedCheck_1899_ = (!crate::leanh::lean_is_exclusive(v___x_1877_)) as u8;
                    if v_isSharedCheck_1899_ == 0 {
                        v___x_1894_ = v___x_1877_;
                        v_isShared_1895_ = v_isSharedCheck_1899_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1892_);
                        crate::leanh::lean_dec(v___x_1877_);
                        v___x_1894_ = crate::leanh::lean_box(0);
                        v_isShared_1895_ = v_isSharedCheck_1899_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1895_ == 0 {
                    v___x_1897_ = v___x_1894_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1898_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
                    v___x_1897_ = v_reuseFailAlloc_1898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg___boxed(
    mut v_ref_1900_: *mut crate::leanh::LeanObject,
    mut v_msg_1901_: *mut crate::leanh::LeanObject,
    mut v___y_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_ref_1900_, v_msg_1901_, v___y_1902_, v___y_1903_);
    crate::leanh::lean_dec(v___y_1903_);
    crate::leanh::lean_dec_ref(v___y_1902_);
    crate::leanh::lean_dec(v_ref_1900_);
    return v_res_1905_;
}
pub unsafe fn _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__2;
    v___x_1913_ = l_Lean_stringToMessageData(v___x_1912_);
    return v___x_1913_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf(
    mut v_stx_1917_: *mut crate::leanh::LeanObject,
    mut v_a_1918_: *mut crate::leanh::LeanObject,
    mut v_a_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: u8 = 0;
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1945_: u8 = 0;
    let mut v_ref_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1952_: u8 = 0;
    let mut v___x_1953_: u8 = 0;
    let mut v_val_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1966_: u8 = 0;
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1970_: u8 = 0;
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1990_: u8 = 0;
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_a_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut v_a_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: u8 = 0;
    let mut v___x_2011_: u8 = 0;
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1921_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1;
                crate::leanh::lean_inc(v_stx_1917_);
                v___x_1922_ = l_Lean_Syntax_isOfKind(v_stx_1917_, v___x_1921_);
                if v___x_1922_ == 0 {
                    v___x_1923_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3_once
                        ),
                        _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3,
                    );
                    v___x_1924_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_stx_1917_, v___x_1923_, v_a_1918_, v_a_1919_);
                    crate::leanh::lean_dec(v_stx_1917_);
                    return v___x_1924_;
                } else {
                    v___x_1925_ = crate::leanh::lean_unsigned_to_nat(2);
                    v_c_1926_ = l_Lean_Syntax_getArg(v_stx_1917_, v___x_1925_);
                    crate::leanh::lean_inc(v_c_1926_);
                    v___f_1927_ = crate::leanh::lean_alloc_closure(
                        l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0___boxed
                            as *mut core::ffi::c_void,
                        9,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_1927_, 0, v_c_1926_);
                    v___x_1928_ = crate::leanh::lean_unsigned_to_nat(4);
                    v_t_1929_ = l_Lean_Syntax_getArg(v_stx_1917_, v___x_1928_);
                    v___x_2008_ = crate::leanh::lean_unsigned_to_nat(5);
                    v___x_2009_ = l_Lean_Syntax_getArg(v_stx_1917_, v___x_2008_);
                    v___x_2010_ = l_Lean_Syntax_isNone(v___x_2009_);
                    if v___x_2010_ == 0 {
                        crate::leanh::lean_inc(v___x_2009_);
                        v___x_2011_ = l_Lean_Syntax_matchesNull(v___x_2009_, v___x_1925_);
                        if v___x_2011_ == 0 {
                            crate::leanh::lean_dec(v___x_2009_);
                            crate::leanh::lean_dec(v_t_1929_);
                            crate::leanh::lean_dec_ref(v___f_1927_);
                            crate::leanh::lean_dec(v_c_1926_);
                            v___x_2012_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3), core::ptr::addr_of_mut!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3_once), _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3);
                            v___x_2013_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_stx_1917_, v___x_2012_, v_a_1918_, v_a_1919_);
                            crate::leanh::lean_dec(v_stx_1917_);
                            return v___x_2013_;
                        } else {
                            crate::leanh::lean_dec(v_stx_1917_);
                            v___x_2014_ = crate::leanh::lean_unsigned_to_nat(1);
                            v_e_x3f_2015_ = l_Lean_Syntax_getArg(v___x_2009_, v___x_2014_);
                            crate::leanh::lean_dec(v___x_2009_);
                            v___x_2016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2016_, 0, v_e_x3f_2015_);
                            v_e_x3f_1931_ = v___x_2016_;
                            v___y_1932_ = v_a_1918_;
                            v___y_1933_ = v_a_1919_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2009_);
                        crate::leanh::lean_dec(v_stx_1917_);
                        v___x_2017_ = crate::leanh::lean_box(0);
                        v_e_x3f_1931_ = v___x_2017_;
                        v___y_1932_ = v_a_1918_;
                        v___y_1933_ = v_a_1919_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1934_ = l_Lean_Elab_Command_getRef___redArg(v___y_1932_);
                if crate::leanh::lean_obj_tag(v___x_1934_) == 0 {
                    v_a_1935_ = crate::leanh::lean_ctor_get(v___x_1934_, 0);
                    crate::leanh::lean_inc(v_a_1935_);
                    crate::leanh::lean_dec_ref_known(v___x_1934_, 1);
                    v_fileName_1936_ = crate::leanh::lean_ctor_get(v___y_1932_, 0);
                    v_fileMap_1937_ = crate::leanh::lean_ctor_get(v___y_1932_, 1);
                    v_currRecDepth_1938_ = crate::leanh::lean_ctor_get(v___y_1932_, 2);
                    v_cmdPos_1939_ = crate::leanh::lean_ctor_get(v___y_1932_, 3);
                    v_macroStack_1940_ = crate::leanh::lean_ctor_get(v___y_1932_, 4);
                    v_quotContext_x3f_1941_ = crate::leanh::lean_ctor_get(v___y_1932_, 5);
                    v_currMacroScope_1942_ = crate::leanh::lean_ctor_get(v___y_1932_, 6);
                    v_snap_x3f_1943_ = crate::leanh::lean_ctor_get(v___y_1932_, 8);
                    v_cancelTk_x3f_1944_ = crate::leanh::lean_ctor_get(v___y_1932_, 9);
                    v_suppressElabErrors_1945_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1932_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_1946_ = l_Lean_replaceRef(v_c_1926_, v_a_1935_);
                    crate::leanh::lean_dec(v_a_1935_);
                    crate::leanh::lean_dec(v_c_1926_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_1944_);
                    crate::leanh::lean_inc(v_snap_x3f_1943_);
                    crate::leanh::lean_inc(v_currMacroScope_1942_);
                    crate::leanh::lean_inc(v_quotContext_x3f_1941_);
                    crate::leanh::lean_inc(v_macroStack_1940_);
                    crate::leanh::lean_inc(v_cmdPos_1939_);
                    crate::leanh::lean_inc(v_currRecDepth_1938_);
                    crate::leanh::lean_inc_ref(v_fileMap_1937_);
                    crate::leanh::lean_inc_ref(v_fileName_1936_);
                    v___x_1947_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1947_, 0, v_fileName_1936_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 1, v_fileMap_1937_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 2, v_currRecDepth_1938_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 3, v_cmdPos_1939_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 4, v_macroStack_1940_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 5, v_quotContext_x3f_1941_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 6, v_currMacroScope_1942_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 7, v_ref_1946_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 8, v_snap_x3f_1943_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 9, v_cancelTk_x3f_1944_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1947_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_1945_,
                    );
                    v___x_1948_ = l_Lean_Elab_Command_runTermElabM___redArg(
                        v___f_1927_,
                        v___x_1947_,
                        v___y_1933_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_1947_, 10);
                    if crate::leanh::lean_obj_tag(v___x_1948_) == 0 {
                        v_a_1949_ = crate::leanh::lean_ctor_get(v___x_1948_, 0);
                        v_isSharedCheck_1991_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1948_)) as u8;
                        if v_isSharedCheck_1991_ == 0 {
                            v___x_1951_ = v___x_1948_;
                            v_isShared_1952_ = v_isSharedCheck_1991_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1949_);
                            crate::leanh::lean_dec(v___x_1948_);
                            v___x_1951_ = crate::leanh::lean_box(0);
                            v_isShared_1952_ = v_isSharedCheck_1991_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_e_x3f_1931_);
                        crate::leanh::lean_dec(v_t_1929_);
                        v_a_1992_ = crate::leanh::lean_ctor_get(v___x_1948_, 0);
                        v_isSharedCheck_1999_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1948_)) as u8;
                        if v_isSharedCheck_1999_ == 0 {
                            v___x_1994_ = v___x_1948_;
                            v_isShared_1995_ = v_isSharedCheck_1999_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1992_);
                            crate::leanh::lean_dec(v___x_1948_);
                            v___x_1994_ = crate::leanh::lean_box(0);
                            v_isShared_1995_ = v_isSharedCheck_1999_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_e_x3f_1931_);
                    crate::leanh::lean_dec(v_t_1929_);
                    crate::leanh::lean_dec_ref(v___f_1927_);
                    crate::leanh::lean_dec(v_c_1926_);
                    v_a_2000_ = crate::leanh::lean_ctor_get(v___x_1934_, 0);
                    v_isSharedCheck_2007_ = (!crate::leanh::lean_is_exclusive(v___x_1934_)) as u8;
                    if v_isSharedCheck_2007_ == 0 {
                        v___x_2002_ = v___x_1934_;
                        v_isShared_2003_ = v_isSharedCheck_2007_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2000_);
                        crate::leanh::lean_dec(v___x_1934_);
                        v___x_2002_ = crate::leanh::lean_box(0);
                        v_isShared_2003_ = v_isSharedCheck_2007_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1953_ = (crate::leanh::lean_unbox(v_a_1949_) as u8);
                crate::leanh::lean_dec(v_a_1949_);
                if v___x_1953_ == 0 {
                    crate::leanh::lean_dec(v_t_1929_);
                    if crate::leanh::lean_obj_tag(v_e_x3f_1931_) == 1 {
                        crate::leanh::lean_del_object(v___x_1951_);
                        v_val_1954_ = crate::leanh::lean_ctor_get(v_e_x3f_1931_, 0);
                        crate::leanh::lean_inc(v_val_1954_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_1931_, 1);
                        v___x_1955_ = l_Lean_Elab_Command_getRef___redArg(v___y_1932_);
                        if crate::leanh::lean_obj_tag(v___x_1955_) == 0 {
                            v_a_1956_ = crate::leanh::lean_ctor_get(v___x_1955_, 0);
                            crate::leanh::lean_inc(v_a_1956_);
                            crate::leanh::lean_dec_ref_known(v___x_1955_, 1);
                            v___x_1957_ =
                                l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo(v_val_1954_);
                            v___x_1958_ =
                                l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__5;
                            v___x_1959_ = crate::leanh::lean_box(2);
                            v___x_1960_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1960_, 0, v___x_1959_);
                            crate::leanh::lean_ctor_set(v___x_1960_, 1, v___x_1958_);
                            crate::leanh::lean_ctor_set(v___x_1960_, 2, v___x_1957_);
                            crate::leanh::lean_inc_ref(v___x_1960_);
                            v___x_1961_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_Command_elabCommand___boxed as *mut core::ffi::c_void,
                                4,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___x_1961_, 0, v___x_1960_);
                            v___x_1962_ = l_Lean_Elab_Command_withMacroExpansion___redArg(
                                v_a_1956_,
                                v___x_1960_,
                                v___x_1961_,
                                v___y_1932_,
                                v___y_1933_,
                            );
                            return v___x_1962_;
                        } else {
                            crate::leanh::lean_dec(v_val_1954_);
                            v_a_1963_ = crate::leanh::lean_ctor_get(v___x_1955_, 0);
                            v_isSharedCheck_1970_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1955_)) as u8;
                            if v_isSharedCheck_1970_ == 0 {
                                v___x_1965_ = v___x_1955_;
                                v_isShared_1966_ = v_isSharedCheck_1970_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1963_);
                                crate::leanh::lean_dec(v___x_1955_);
                                v___x_1965_ = crate::leanh::lean_box(0);
                                v_isShared_1966_ = v_isSharedCheck_1970_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_e_x3f_1931_);
                        v___x_1971_ = crate::leanh::lean_box(0);
                        if v_isShared_1952_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1951_, 0, v___x_1971_);
                            v___x_1973_ = v___x_1951_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1974_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1971_);
                            v___x_1973_ = v_reuseFailAlloc_1974_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1951_);
                    crate::leanh::lean_dec(v_e_x3f_1931_);
                    v___x_1975_ = l_Lean_Elab_Command_getRef___redArg(v___y_1932_);
                    if crate::leanh::lean_obj_tag(v___x_1975_) == 0 {
                        v_a_1976_ = crate::leanh::lean_ctor_get(v___x_1975_, 0);
                        crate::leanh::lean_inc(v_a_1976_);
                        crate::leanh::lean_dec_ref_known(v___x_1975_, 1);
                        v___x_1977_ = l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo(v_t_1929_);
                        v___x_1978_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__5;
                        v___x_1979_ = crate::leanh::lean_box(2);
                        v___x_1980_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1980_, 0, v___x_1979_);
                        crate::leanh::lean_ctor_set(v___x_1980_, 1, v___x_1978_);
                        crate::leanh::lean_ctor_set(v___x_1980_, 2, v___x_1977_);
                        crate::leanh::lean_inc_ref(v___x_1980_);
                        v___x_1981_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Command_elabCommand___boxed as *mut core::ffi::c_void,
                            4,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___x_1981_, 0, v___x_1980_);
                        v___x_1982_ = l_Lean_Elab_Command_withMacroExpansion___redArg(
                            v_a_1976_,
                            v___x_1980_,
                            v___x_1981_,
                            v___y_1932_,
                            v___y_1933_,
                        );
                        return v___x_1982_;
                    } else {
                        crate::leanh::lean_dec(v_t_1929_);
                        v_a_1983_ = crate::leanh::lean_ctor_get(v___x_1975_, 0);
                        v_isSharedCheck_1990_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1975_)) as u8;
                        if v_isSharedCheck_1990_ == 0 {
                            v___x_1985_ = v___x_1975_;
                            v_isShared_1986_ = v_isSharedCheck_1990_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1983_);
                            crate::leanh::lean_dec(v___x_1975_);
                            v___x_1985_ = crate::leanh::lean_box(0);
                            v_isShared_1986_ = v_isSharedCheck_1990_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_1966_ == 0 {
                    v___x_1968_ = v___x_1965_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1969_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
                    v___x_1968_ = v_reuseFailAlloc_1969_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1968_;
            }
            5 => {
                return v___x_1973_;
            }
            6 => {
                if v_isShared_1986_ == 0 {
                    v___x_1988_ = v___x_1985_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1989_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
                    v___x_1988_ = v_reuseFailAlloc_1989_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1988_;
            }
            8 => {
                if v_isShared_1995_ == 0 {
                    v___x_1997_ = v___x_1994_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1998_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
                    v___x_1997_ = v_reuseFailAlloc_1998_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1997_;
            }
            10 => {
                if v_isShared_2003_ == 0 {
                    v___x_2005_ = v___x_2002_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
                    v___x_2005_ = v_reuseFailAlloc_2006_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___boxed(
    mut v_stx_2018_: *mut crate::leanh::LeanObject,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
    mut v_a_2020_: *mut crate::leanh::LeanObject,
    mut v_a_2021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2022_ =
        l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf(v_stx_2018_, v_a_2019_, v_a_2020_);
    crate::leanh::lean_dec(v_a_2020_);
    crate::leanh::lean_dec_ref(v_a_2019_);
    return v_res_2022_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0(
    mut v_00_u03b1_2023_: *mut crate::leanh::LeanObject,
    mut v_ref_2024_: *mut crate::leanh::LeanObject,
    mut v_msg_2025_: *mut crate::leanh::LeanObject,
    mut v___y_2026_: *mut crate::leanh::LeanObject,
    mut v___y_2027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2029_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_ref_2024_, v_msg_2025_, v___y_2026_, v___y_2027_);
    return v___x_2029_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___boxed(
    mut v_00_u03b1_2030_: *mut crate::leanh::LeanObject,
    mut v_ref_2031_: *mut crate::leanh::LeanObject,
    mut v_msg_2032_: *mut crate::leanh::LeanObject,
    mut v___y_2033_: *mut crate::leanh::LeanObject,
    mut v___y_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2036_ =
        l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0(
            v_00_u03b1_2030_,
            v_ref_2031_,
            v_msg_2032_,
            v___y_2033_,
            v___y_2034_,
        );
    crate::leanh::lean_dec(v___y_2034_);
    crate::leanh::lean_dec_ref(v___y_2033_);
    crate::leanh::lean_dec(v_ref_2031_);
    return v_res_2036_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1(
    mut v_msgData_2037_: *mut crate::leanh::LeanObject,
    mut v___y_2038_: *mut crate::leanh::LeanObject,
    mut v___y_2039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(v_msgData_2037_, v___y_2039_);
    return v___x_2041_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_2042_: *mut crate::leanh::LeanObject,
    mut v___y_2043_: *mut crate::leanh::LeanObject,
    mut v___y_2044_: *mut crate::leanh::LeanObject,
    mut v___y_2045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2046_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1(v_msgData_2042_, v___y_2043_, v___y_2044_);
    crate::leanh::lean_dec(v___y_2044_);
    crate::leanh::lean_dec_ref(v___y_2043_);
    return v_res_2046_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0(
    mut v_00_u03b1_2047_: *mut crate::leanh::LeanObject,
    mut v_msg_2048_: *mut crate::leanh::LeanObject,
    mut v___y_2049_: *mut crate::leanh::LeanObject,
    mut v___y_2050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2052_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(v_msg_2048_, v___y_2049_, v___y_2050_);
    return v___x_2052_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___boxed(
    mut v_00_u03b1_2053_: *mut crate::leanh::LeanObject,
    mut v_msg_2054_: *mut crate::leanh::LeanObject,
    mut v___y_2055_: *mut crate::leanh::LeanObject,
    mut v___y_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2058_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0(v_00_u03b1_2053_, v_msg_2054_, v___y_2055_, v___y_2056_);
    crate::leanh::lean_dec(v___y_2056_);
    crate::leanh::lean_dec_ref(v___y_2055_);
    return v_res_2058_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2(
    mut v_msgData_2059_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2060_: *mut crate::leanh::LeanObject,
    mut v___y_2061_: *mut crate::leanh::LeanObject,
    mut v___y_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2064_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(v_msgData_2059_, v_macroStack_2060_, v___y_2062_);
    return v___x_2064_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_2065_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2066_: *mut crate::leanh::LeanObject,
    mut v___y_2067_: *mut crate::leanh::LeanObject,
    mut v___y_2068_: *mut crate::leanh::LeanObject,
    mut v___y_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2070_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2(v_msgData_2065_, v_macroStack_2066_, v___y_2067_, v___y_2068_);
    crate::leanh::lean_dec(v___y_2068_);
    crate::leanh::lean_dec_ref(v___y_2067_);
    return v_res_2070_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2099_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2100_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1;
    v___x_2101_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__10;
    v___x_2102_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2103_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2099_,
        v___x_2100_,
        v___x_2101_,
        v___x_2102_,
    );
    return v___x_2103_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___boxed(
    mut v_a_2104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2105_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1();
    return v_res_2105_;
}
pub unsafe fn l_Lake_DSL_toExprIO___redArg(
    mut v_inst_2106_: *mut crate::leanh::LeanObject,
    mut v_x_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toExpr_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2119_: u8 = 0;
    let mut v_a_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toExpr_2109_ = crate::leanh::lean_ctor_get(v_inst_2106_, 0);
                crate::leanh::lean_inc_ref(v_toExpr_2109_);
                crate::leanh::lean_dec_ref(v_inst_2106_);
                v___x_2110_ = crate::leanh::lean_apply_1(v_x_2107_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_2110_) == 0 {
                    v_a_2111_ = crate::leanh::lean_ctor_get(v___x_2110_, 0);
                    v_isSharedCheck_2119_ = (!crate::leanh::lean_is_exclusive(v___x_2110_)) as u8;
                    if v_isSharedCheck_2119_ == 0 {
                        v___x_2113_ = v___x_2110_;
                        v_isShared_2114_ = v_isSharedCheck_2119_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2111_);
                        crate::leanh::lean_dec(v___x_2110_);
                        v___x_2113_ = crate::leanh::lean_box(0);
                        v_isShared_2114_ = v_isSharedCheck_2119_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_toExpr_2109_);
                    v_a_2120_ = crate::leanh::lean_ctor_get(v___x_2110_, 0);
                    v_isSharedCheck_2127_ = (!crate::leanh::lean_is_exclusive(v___x_2110_)) as u8;
                    if v_isSharedCheck_2127_ == 0 {
                        v___x_2122_ = v___x_2110_;
                        v_isShared_2123_ = v_isSharedCheck_2127_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2120_);
                        crate::leanh::lean_dec(v___x_2110_);
                        v___x_2122_ = crate::leanh::lean_box(0);
                        v_isShared_2123_ = v_isSharedCheck_2127_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2115_ = crate::leanh::lean_apply_1(v_toExpr_2109_, v_a_2111_);
                if v_isShared_2114_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2113_, 0, v___x_2115_);
                    v___x_2117_ = v___x_2113_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2118_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
                    v___x_2117_ = v_reuseFailAlloc_2118_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2117_;
            }
            3 => {
                if v_isShared_2123_ == 0 {
                    v___x_2125_ = v___x_2122_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
                    v___x_2125_ = v_reuseFailAlloc_2126_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_DSL_toExprIO___redArg___boxed(
    mut v_inst_2128_: *mut crate::leanh::LeanObject,
    mut v_x_2129_: *mut crate::leanh::LeanObject,
    mut v_a_2130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2131_ = l_Lake_DSL_toExprIO___redArg(v_inst_2128_, v_x_2129_);
    return v_res_2131_;
}
pub unsafe fn l_Lake_DSL_toExprIO(
    mut v_00_u03b1_2132_: *mut crate::leanh::LeanObject,
    mut v_inst_2133_: *mut crate::leanh::LeanObject,
    mut v_x_2134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2136_ = l_Lake_DSL_toExprIO___redArg(v_inst_2133_, v_x_2134_);
    return v___x_2136_;
}
pub unsafe fn l_Lake_DSL_toExprIO___boxed(
    mut v_00_u03b1_2137_: *mut crate::leanh::LeanObject,
    mut v_inst_2138_: *mut crate::leanh::LeanObject,
    mut v_x_2139_: *mut crate::leanh::LeanObject,
    mut v_a_2140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2141_ = l_Lake_DSL_toExprIO(v_00_u03b1_2137_, v_inst_2138_, v_x_2139_);
    return v_res_2141_;
}
pub unsafe fn _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2145_ = crate::leanh::lean_box(0);
    v___x_2146_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__1;
    v___x_2147_ = l_Lean_mkConst(v___x_2146_, v___x_2145_);
    return v___x_2147_;
}
pub unsafe fn _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = crate::leanh::lean_box(0);
    v___x_2154_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5;
    v___x_2155_ = l_Lean_mkConst(v___x_2154_, v___x_2153_);
    return v___x_2155_;
}
pub unsafe fn _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2156_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6_once
        ),
        _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6,
    );
    v___x_2157_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2_once
        ),
        _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2,
    );
    v___x_2158_ = l_Lean_Expr_app___override(v___x_2157_, v___x_2156_);
    return v___x_2158_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1(
    mut v_v_2159_: *mut crate::leanh::LeanObject,
    mut v_a_2160_: *mut crate::leanh::LeanObject,
    mut v_a_2161_: *mut crate::leanh::LeanObject,
    mut v_a_2162_: *mut crate::leanh::LeanObject,
    mut v_a_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: u8 = 0;
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2165_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7_once
        ),
        _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7,
    );
    v___x_2166_ = 1;
    v___x_2167_ = 1;
    v___x_2168_ = l_Lean_Meta_evalExpr___redArg(
        v___x_2165_,
        v_v_2159_,
        v___x_2166_,
        v___x_2167_,
        v_a_2160_,
        v_a_2161_,
        v_a_2162_,
        v_a_2163_,
    );
    return v___x_2168_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___boxed(
    mut v_v_2169_: *mut crate::leanh::LeanObject,
    mut v_a_2170_: *mut crate::leanh::LeanObject,
    mut v_a_2171_: *mut crate::leanh::LeanObject,
    mut v_a_2172_: *mut crate::leanh::LeanObject,
    mut v_a_2173_: *mut crate::leanh::LeanObject,
    mut v_a_2174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2175_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1(
        v_v_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_,
    );
    crate::leanh::lean_dec(v_a_2173_);
    crate::leanh::lean_dec_ref(v_a_2172_);
    crate::leanh::lean_dec(v_a_2171_);
    crate::leanh::lean_dec_ref(v_a_2170_);
    return v_res_2175_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2176_ = crate::leanh::lean_box(0);
    v___x_2177_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2178_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2178_, 0, v___x_2177_);
    crate::leanh::lean_ctor_set(v___x_2178_, 1, v___x_2176_);
    return v___x_2178_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0);
    v___x_2181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2181_, 0, v___x_2180_);
    return v___x_2181_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___boxed(
    mut v___y_2182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2183_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg();
    return v_res_2183_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0(
    mut v_00_u03b1_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
    mut v___y_2187_: *mut crate::leanh::LeanObject,
    mut v___y_2188_: *mut crate::leanh::LeanObject,
    mut v___y_2189_: *mut crate::leanh::LeanObject,
    mut v___y_2190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2192_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg();
    return v___x_2192_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___boxed(
    mut v_00_u03b1_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
    mut v___y_2198_: *mut crate::leanh::LeanObject,
    mut v___y_2199_: *mut crate::leanh::LeanObject,
    mut v___y_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0(v_00_u03b1_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
    crate::leanh::lean_dec(v___y_2199_);
    crate::leanh::lean_dec_ref(v___y_2198_);
    crate::leanh::lean_dec(v___y_2197_);
    crate::leanh::lean_dec_ref(v___y_2196_);
    crate::leanh::lean_dec(v___y_2195_);
    crate::leanh::lean_dec_ref(v___y_2194_);
    return v_res_2201_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(
    mut v_e_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2205_: u8 = 0;
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut v_unused_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2205_ = l_Lean_Expr_hasMVar(v_e_2202_);
                if v___x_2205_ == 0 {
                    v___x_2206_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2206_, 0, v_e_2202_);
                    return v___x_2206_;
                } else {
                    v___x_2207_ = lean_st_ref_get(v___y_2203_);
                    v_mctx_2208_ = crate::leanh::lean_ctor_get(v___x_2207_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2208_);
                    crate::leanh::lean_dec(v___x_2207_);
                    v___x_2209_ = l_Lean_instantiateMVarsCore(v_mctx_2208_, v_e_2202_);
                    v_fst_2210_ = crate::leanh::lean_ctor_get(v___x_2209_, 0);
                    crate::leanh::lean_inc(v_fst_2210_);
                    v_snd_2211_ = crate::leanh::lean_ctor_get(v___x_2209_, 1);
                    crate::leanh::lean_inc(v_snd_2211_);
                    crate::leanh::lean_dec_ref(v___x_2209_);
                    v___x_2212_ = lean_st_ref_take(v___y_2203_);
                    v_cache_2213_ = crate::leanh::lean_ctor_get(v___x_2212_, 1);
                    v_zetaDeltaFVarIds_2214_ = crate::leanh::lean_ctor_get(v___x_2212_, 2);
                    v_postponed_2215_ = crate::leanh::lean_ctor_get(v___x_2212_, 3);
                    v_diag_2216_ = crate::leanh::lean_ctor_get(v___x_2212_, 4);
                    v_isSharedCheck_2225_ = (!crate::leanh::lean_is_exclusive(v___x_2212_)) as u8;
                    if v_isSharedCheck_2225_ == 0 {
                        v_unused_2226_ = crate::leanh::lean_ctor_get(v___x_2212_, 0);
                        crate::leanh::lean_dec(v_unused_2226_);
                        v___x_2218_ = v___x_2212_;
                        v_isShared_2219_ = v_isSharedCheck_2225_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2216_);
                        crate::leanh::lean_inc(v_postponed_2215_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2214_);
                        crate::leanh::lean_inc(v_cache_2213_);
                        crate::leanh::lean_dec(v___x_2212_);
                        v___x_2218_ = crate::leanh::lean_box(0);
                        v_isShared_2219_ = v_isSharedCheck_2225_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2219_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2218_, 0, v_snd_2211_);
                    v___x_2221_ = v___x_2218_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2224_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_snd_2211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_cache_2213_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2224_,
                        2,
                        v_zetaDeltaFVarIds_2214_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_postponed_2215_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_diag_2216_);
                    v___x_2221_ = v_reuseFailAlloc_2224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2222_ = lean_st_ref_set(v___y_2203_, v___x_2221_);
                v___x_2223_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2223_, 0, v_fst_2210_);
                return v___x_2223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg___boxed(
    mut v_e_2227_: *mut crate::leanh::LeanObject,
    mut v___y_2228_: *mut crate::leanh::LeanObject,
    mut v___y_2229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2230_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(v_e_2227_, v___y_2228_);
    crate::leanh::lean_dec(v___y_2228_);
    return v_res_2230_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1(
    mut v_e_2231_: *mut crate::leanh::LeanObject,
    mut v___y_2232_: *mut crate::leanh::LeanObject,
    mut v___y_2233_: *mut crate::leanh::LeanObject,
    mut v___y_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2239_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(v_e_2231_, v___y_2235_);
    return v___x_2239_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___boxed(
    mut v_e_2240_: *mut crate::leanh::LeanObject,
    mut v___y_2241_: *mut crate::leanh::LeanObject,
    mut v___y_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
    mut v___y_2244_: *mut crate::leanh::LeanObject,
    mut v___y_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2248_ =
        l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1(
            v_e_2240_,
            v___y_2241_,
            v___y_2242_,
            v___y_2243_,
            v___y_2244_,
            v___y_2245_,
            v___y_2246_,
        );
    crate::leanh::lean_dec(v___y_2246_);
    crate::leanh::lean_dec_ref(v___y_2245_);
    crate::leanh::lean_dec(v___y_2244_);
    crate::leanh::lean_dec_ref(v___y_2243_);
    crate::leanh::lean_dec(v___y_2242_);
    crate::leanh::lean_dec_ref(v___y_2241_);
    return v_res_2248_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2249_ = crate::leanh::lean_box(0);
    v___x_2250_ = l_Lean_Elab_abortTermExceptionId;
    v___x_2251_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2251_, 0, v___x_2250_);
    crate::leanh::lean_ctor_set(v___x_2251_, 1, v___x_2249_);
    return v___x_2251_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0);
    v___x_2254_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2254_, 0, v___x_2253_);
    return v___x_2254_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___boxed(
    mut v___y_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2256_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg();
    return v_res_2256_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5(
    mut v_00_u03b1_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
    mut v___y_2259_: *mut crate::leanh::LeanObject,
    mut v___y_2260_: *mut crate::leanh::LeanObject,
    mut v___y_2261_: *mut crate::leanh::LeanObject,
    mut v___y_2262_: *mut crate::leanh::LeanObject,
    mut v___y_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2265_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg();
    return v___x_2265_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___boxed(
    mut v_00_u03b1_2266_: *mut crate::leanh::LeanObject,
    mut v___y_2267_: *mut crate::leanh::LeanObject,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
    mut v___y_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2274_ =
        l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5(
            v_00_u03b1_2266_,
            v___y_2267_,
            v___y_2268_,
            v___y_2269_,
            v___y_2270_,
            v___y_2271_,
            v___y_2272_,
        );
    crate::leanh::lean_dec(v___y_2272_);
    crate::leanh::lean_dec_ref(v___y_2271_);
    crate::leanh::lean_dec(v___y_2270_);
    crate::leanh::lean_dec_ref(v___y_2269_);
    crate::leanh::lean_dec(v___y_2268_);
    crate::leanh::lean_dec_ref(v___y_2267_);
    return v_res_2274_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0(
    mut v_a_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
    mut v___y_2277_: *mut crate::leanh::LeanObject,
    mut v___y_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
    mut v___y_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2287_: u8 = 0;
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2292_: u8 = 0;
    let mut v_a_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2296_: u8 = 0;
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2283_ = crate::leanh::lean_apply_1(v_a_2275_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_2283_) == 0 {
                    v_a_2284_ = crate::leanh::lean_ctor_get(v___x_2283_, 0);
                    v_isSharedCheck_2292_ = (!crate::leanh::lean_is_exclusive(v___x_2283_)) as u8;
                    if v_isSharedCheck_2292_ == 0 {
                        v___x_2286_ = v___x_2283_;
                        v_isShared_2287_ = v_isSharedCheck_2292_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2284_);
                        crate::leanh::lean_dec(v___x_2283_);
                        v___x_2286_ = crate::leanh::lean_box(0);
                        v_isShared_2287_ = v_isSharedCheck_2292_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2293_ = crate::leanh::lean_ctor_get(v___x_2283_, 0);
                    v_isSharedCheck_2301_ = (!crate::leanh::lean_is_exclusive(v___x_2283_)) as u8;
                    if v_isSharedCheck_2301_ == 0 {
                        v___x_2295_ = v___x_2283_;
                        v_isShared_2296_ = v_isSharedCheck_2301_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2293_);
                        crate::leanh::lean_dec(v___x_2283_);
                        v___x_2295_ = crate::leanh::lean_box(0);
                        v_isShared_2296_ = v_isSharedCheck_2301_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2288_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2288_, 0, v_a_2284_);
                if v_isShared_2287_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2286_, 0, v___x_2288_);
                    v___x_2290_ = v___x_2286_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
                    v___x_2290_ = v_reuseFailAlloc_2291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2290_;
            }
            3 => {
                v___x_2297_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2297_, 0, v_a_2293_);
                if v_isShared_2296_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2295_, 0);
                    crate::leanh::lean_ctor_set(v___x_2295_, 0, v___x_2297_);
                    v___x_2299_ = v___x_2295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
                    v___x_2299_ = v_reuseFailAlloc_2300_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0___boxed(
    mut v_a_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
    mut v___y_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2310_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0(
        v_a_2302_,
        v___y_2303_,
        v___y_2304_,
        v___y_2305_,
        v___y_2306_,
        v___y_2307_,
        v___y_2308_,
    );
    crate::leanh::lean_dec(v___y_2308_);
    crate::leanh::lean_dec_ref(v___y_2307_);
    crate::leanh::lean_dec(v___y_2306_);
    crate::leanh::lean_dec_ref(v___y_2305_);
    crate::leanh::lean_dec(v___y_2304_);
    crate::leanh::lean_dec_ref(v___y_2303_);
    return v_res_2310_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(
    mut v_msgData_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2317_ = lean_st_ref_get(v___y_2315_);
    v_env_2318_ = crate::leanh::lean_ctor_get(v___x_2317_, 0);
    crate::leanh::lean_inc_ref(v_env_2318_);
    crate::leanh::lean_dec(v___x_2317_);
    v___x_2319_ = lean_st_ref_get(v___y_2313_);
    v_mctx_2320_ = crate::leanh::lean_ctor_get(v___x_2319_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2320_);
    crate::leanh::lean_dec(v___x_2319_);
    v_lctx_2321_ = crate::leanh::lean_ctor_get(v___y_2312_, 2);
    v_options_2322_ = crate::leanh::lean_ctor_get(v___y_2314_, 2);
    crate::leanh::lean_inc_ref(v_options_2322_);
    crate::leanh::lean_inc_ref(v_lctx_2321_);
    v___x_2323_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2323_, 0, v_env_2318_);
    crate::leanh::lean_ctor_set(v___x_2323_, 1, v_mctx_2320_);
    crate::leanh::lean_ctor_set(v___x_2323_, 2, v_lctx_2321_);
    crate::leanh::lean_ctor_set(v___x_2323_, 3, v_options_2322_);
    v___x_2324_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2324_, 0, v___x_2323_);
    crate::leanh::lean_ctor_set(v___x_2324_, 1, v_msgData_2311_);
    v___x_2325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2325_, 0, v___x_2324_);
    return v___x_2325_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9___boxed(
    mut v_msgData_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2332_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(v_msgData_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
    crate::leanh::lean_dec(v___y_2330_);
    crate::leanh::lean_dec_ref(v___y_2329_);
    crate::leanh::lean_dec(v___y_2328_);
    crate::leanh::lean_dec_ref(v___y_2327_);
    return v_res_2332_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0(
    mut v___y_2341_: u8,
    mut v_suppressElabErrors_2342_: u8,
    mut v_x_2343_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2343_) == 1 {
        let mut v_pre_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_2344_ = crate::leanh::lean_ctor_get(v_x_2343_, 0);
        match crate::leanh::lean_obj_tag(v_pre_2344_) {
            1 => {
                let mut v_pre_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_2345_ = crate::leanh::lean_ctor_get(v_pre_2344_, 0);
                match crate::leanh::lean_obj_tag(v_pre_2345_) {
                    0 => {
                        let mut v_str_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2349_: u8 = 0;
                        v_str_2346_ = crate::leanh::lean_ctor_get(v_x_2343_, 1);
                        v_str_2347_ = crate::leanh::lean_ctor_get(v_pre_2344_, 1);
                        v___x_2348_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__0;
                        v___x_2349_ = lean_string_dec_eq(v_str_2347_, v___x_2348_);
                        if v___x_2349_ == 0 {
                            let mut v___x_2350_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2351_: u8 = 0;
                            v___x_2350_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__1;
                            v___x_2351_ = lean_string_dec_eq(v_str_2347_, v___x_2350_);
                            if v___x_2351_ == 0 {
                                return v___y_2341_;
                            } else {
                                let mut v___x_2352_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2353_: u8 = 0;
                                v___x_2352_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__2;
                                v___x_2353_ = lean_string_dec_eq(v_str_2346_, v___x_2352_);
                                if v___x_2353_ == 0 {
                                    return v___y_2341_;
                                } else {
                                    return v_suppressElabErrors_2342_;
                                }
                            }
                        } else {
                            let mut v___x_2354_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2355_: u8 = 0;
                            v___x_2354_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__3;
                            v___x_2355_ = lean_string_dec_eq(v_str_2346_, v___x_2354_);
                            if v___x_2355_ == 0 {
                                return v___y_2341_;
                            } else {
                                return v_suppressElabErrors_2342_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_2356_ = crate::leanh::lean_ctor_get(v_pre_2345_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_2356_) == 0 {
                            let mut v_str_2357_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2358_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2359_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2360_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2361_: u8 = 0;
                            v_str_2357_ = crate::leanh::lean_ctor_get(v_x_2343_, 1);
                            v_str_2358_ = crate::leanh::lean_ctor_get(v_pre_2344_, 1);
                            v_str_2359_ = crate::leanh::lean_ctor_get(v_pre_2345_, 1);
                            v___x_2360_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__4;
                            v___x_2361_ = lean_string_dec_eq(v_str_2359_, v___x_2360_);
                            if v___x_2361_ == 0 {
                                return v___y_2341_;
                            } else {
                                let mut v___x_2362_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2363_: u8 = 0;
                                v___x_2362_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__5;
                                v___x_2363_ = lean_string_dec_eq(v_str_2358_, v___x_2362_);
                                if v___x_2363_ == 0 {
                                    return v___y_2341_;
                                } else {
                                    let mut v___x_2364_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2365_: u8 = 0;
                                    v___x_2364_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__6;
                                    v___x_2365_ = lean_string_dec_eq(v_str_2357_, v___x_2364_);
                                    if v___x_2365_ == 0 {
                                        return v___y_2341_;
                                    } else {
                                        return v_suppressElabErrors_2342_;
                                    }
                                }
                            }
                        } else {
                            return v___y_2341_;
                        }
                    }
                    _ => {
                        return v___y_2341_;
                    }
                }
            }
            0 => {
                let mut v_str_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2368_: u8 = 0;
                v_str_2366_ = crate::leanh::lean_ctor_get(v_x_2343_, 1);
                v___x_2367_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__7;
                v___x_2368_ = lean_string_dec_eq(v_str_2366_, v___x_2367_);
                if v___x_2368_ == 0 {
                    return v___y_2341_;
                } else {
                    return v_suppressElabErrors_2342_;
                }
            }
            _ => {
                return v___y_2341_;
            }
        }
    } else {
        return v___y_2341_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___boxed(
    mut v___y_2369_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_2370_: *mut crate::leanh::LeanObject,
    mut v_x_2371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_23274__boxed_2372_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2373_: u8 = 0;
    let mut v_res_2374_: u8 = 0;
    let mut v_r_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_23274__boxed_2372_ = (crate::leanh::lean_unbox(v___y_2369_) as u8);
    v_suppressElabErrors_boxed_2373_ = (crate::leanh::lean_unbox(v_suppressElabErrors_2370_) as u8);
    v_res_2374_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0(v___y_23274__boxed_2372_, v_suppressElabErrors_boxed_2373_, v_x_2371_);
    crate::leanh::lean_dec(v_x_2371_);
    v_r_2375_ = crate::leanh::lean_box((v_res_2374_) as usize);
    return v_r_2375_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(
    mut v_ref_2377_: *mut crate::leanh::LeanObject,
    mut v_msgData_2378_: *mut crate::leanh::LeanObject,
    mut v_severity_2379_: u8,
    mut v_isSilent_2380_: u8,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2389_: u8 = 0;
    let mut v___y_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2393_: u8 = 0;
    let mut v___y_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2410_: u8 = 0;
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2421_: u8 = 0;
    let mut v___y_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2424_: u8 = 0;
    let mut v___y_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2426_: u8 = 0;
    let mut v___y_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2429_: u8 = 0;
    let mut v___y_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2436_: u8 = 0;
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut v___y_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2449_: u8 = 0;
    let mut v___y_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2452_: u8 = 0;
    let mut v___y_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2454_: u8 = 0;
    let mut v___y_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2462_: u8 = 0;
    let mut v___y_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2464_: u8 = 0;
    let mut v___y_2465_: u8 = 0;
    let mut v_ref_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: u8 = 0;
    let mut v___y_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2475_: u8 = 0;
    let mut v___y_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2477_: u8 = 0;
    let mut v___y_2478_: u8 = 0;
    let mut v___y_2480_: u8 = 0;
    let mut v_fileName_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2485_: u8 = 0;
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: u8 = 0;
    let mut v___x_2490_: u8 = 0;
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: u8 = 0;
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2470_ = 2;
                v___x_2495_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2379_, v___x_2470_);
                if v___x_2495_ == 0 {
                    v___y_2480_ = v___x_2495_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_2378_);
                    v___x_2496_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2378_);
                    v___y_2480_ = v___x_2496_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2396_ = lean_st_ref_take(v___y_2395_);
                v_currNamespace_2397_ = crate::leanh::lean_ctor_get(v___y_2394_, 6);
                v_openDecls_2398_ = crate::leanh::lean_ctor_get(v___y_2394_, 7);
                v_env_2399_ = crate::leanh::lean_ctor_get(v___x_2396_, 0);
                v_nextMacroScope_2400_ = crate::leanh::lean_ctor_get(v___x_2396_, 1);
                v_ngen_2401_ = crate::leanh::lean_ctor_get(v___x_2396_, 2);
                v_auxDeclNGen_2402_ = crate::leanh::lean_ctor_get(v___x_2396_, 3);
                v_traceState_2403_ = crate::leanh::lean_ctor_get(v___x_2396_, 4);
                v_cache_2404_ = crate::leanh::lean_ctor_get(v___x_2396_, 5);
                v_messages_2405_ = crate::leanh::lean_ctor_get(v___x_2396_, 6);
                v_infoState_2406_ = crate::leanh::lean_ctor_get(v___x_2396_, 7);
                v_snapshotTasks_2407_ = crate::leanh::lean_ctor_get(v___x_2396_, 8);
                v_isSharedCheck_2421_ = (!crate::leanh::lean_is_exclusive(v___x_2396_)) as u8;
                if v_isSharedCheck_2421_ == 0 {
                    v___x_2409_ = v___x_2396_;
                    v_isShared_2410_ = v_isSharedCheck_2421_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2407_);
                    crate::leanh::lean_inc(v_infoState_2406_);
                    crate::leanh::lean_inc(v_messages_2405_);
                    crate::leanh::lean_inc(v_cache_2404_);
                    crate::leanh::lean_inc(v_traceState_2403_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2402_);
                    crate::leanh::lean_inc(v_ngen_2401_);
                    crate::leanh::lean_inc(v_nextMacroScope_2400_);
                    crate::leanh::lean_inc(v_env_2399_);
                    crate::leanh::lean_dec(v___x_2396_);
                    v___x_2409_ = crate::leanh::lean_box(0);
                    v_isShared_2410_ = v_isSharedCheck_2421_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_2398_);
                crate::leanh::lean_inc(v_currNamespace_2397_);
                v___x_2411_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2411_, 0, v_currNamespace_2397_);
                crate::leanh::lean_ctor_set(v___x_2411_, 1, v_openDecls_2398_);
                v___x_2412_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2412_, 0, v___x_2411_);
                crate::leanh::lean_ctor_set(v___x_2412_, 1, v___y_2387_);
                crate::leanh::lean_inc_ref(v___y_2390_);
                crate::leanh::lean_inc_ref(v___y_2391_);
                v___x_2413_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_2413_, 0, v___y_2391_);
                crate::leanh::lean_ctor_set(v___x_2413_, 1, v___y_2388_);
                crate::leanh::lean_ctor_set(v___x_2413_, 2, v___y_2392_);
                crate::leanh::lean_ctor_set(v___x_2413_, 3, v___y_2390_);
                crate::leanh::lean_ctor_set(v___x_2413_, 4, v___x_2412_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2413_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_2393_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2413_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2389_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2413_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2380_,
                );
                v___x_2414_ = l_Lean_MessageLog_add(v___x_2413_, v_messages_2405_);
                if v_isShared_2410_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2409_, 6, v___x_2414_);
                    v___x_2416_ = v___x_2409_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2420_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_env_2399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_nextMacroScope_2400_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 2, v_ngen_2401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 3, v_auxDeclNGen_2402_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 4, v_traceState_2403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 5, v_cache_2404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 6, v___x_2414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 7, v_infoState_2406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 8, v_snapshotTasks_2407_);
                    v___x_2416_ = v_reuseFailAlloc_2420_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2417_ = lean_st_ref_set(v___y_2395_, v___x_2416_);
                v___x_2418_ = crate::leanh::lean_box(0);
                v___x_2419_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2419_, 0, v___x_2418_);
                return v___x_2419_;
            }
            4 => {
                v___x_2431_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2378_,
                    );
                v___x_2432_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(v___x_2431_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
                v_a_2433_ = crate::leanh::lean_ctor_get(v___x_2432_, 0);
                v_isSharedCheck_2446_ = (!crate::leanh::lean_is_exclusive(v___x_2432_)) as u8;
                if v_isSharedCheck_2446_ == 0 {
                    v___x_2435_ = v___x_2432_;
                    v_isShared_2436_ = v_isSharedCheck_2446_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2433_);
                    crate::leanh::lean_dec(v___x_2432_);
                    v___x_2435_ = crate::leanh::lean_box(0);
                    v_isShared_2436_ = v_isSharedCheck_2446_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_2428_, 2);
                v___x_2437_ = l_Lean_FileMap_toPosition(v___y_2428_, v___y_2427_);
                crate::leanh::lean_dec(v___y_2427_);
                v___x_2438_ = l_Lean_FileMap_toPosition(v___y_2428_, v___y_2430_);
                crate::leanh::lean_dec(v___y_2430_);
                v___x_2439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2439_, 0, v___x_2438_);
                v___x_2440_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___closed__0;
                if v___y_2426_ == 0 {
                    crate::leanh::lean_del_object(v___x_2435_);
                    crate::leanh::lean_dec_ref(v___y_2423_);
                    v___y_2387_ = v_a_2433_;
                    v___y_2388_ = v___x_2437_;
                    v___y_2389_ = v___y_2424_;
                    v___y_2390_ = v___x_2440_;
                    v___y_2391_ = v___y_2425_;
                    v___y_2392_ = v___x_2439_;
                    v___y_2393_ = v___y_2429_;
                    v___y_2394_ = v___y_2383_;
                    v___y_2395_ = v___y_2384_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2433_);
                    v___x_2441_ = l_Lean_MessageData_hasTag(v___y_2423_, v_a_2433_);
                    if v___x_2441_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2439_, 1);
                        crate::leanh::lean_dec_ref(v___x_2437_);
                        crate::leanh::lean_dec(v_a_2433_);
                        v___x_2442_ = crate::leanh::lean_box(0);
                        if v_isShared_2436_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2435_, 0, v___x_2442_);
                            v___x_2444_ = v___x_2435_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2445_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
                            v___x_2444_ = v_reuseFailAlloc_2445_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2435_);
                        v___y_2387_ = v_a_2433_;
                        v___y_2388_ = v___x_2437_;
                        v___y_2389_ = v___y_2424_;
                        v___y_2390_ = v___x_2440_;
                        v___y_2391_ = v___y_2425_;
                        v___y_2392_ = v___x_2439_;
                        v___y_2393_ = v___y_2429_;
                        v___y_2394_ = v___y_2383_;
                        v___y_2395_ = v___y_2384_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2444_;
            }
            7 => {
                v___x_2456_ = l_Lean_Syntax_getTailPos_x3f(v___y_2451_, v___y_2454_);
                crate::leanh::lean_dec(v___y_2451_);
                if crate::leanh::lean_obj_tag(v___x_2456_) == 0 {
                    crate::leanh::lean_inc(v___y_2455_);
                    v___y_2423_ = v___y_2448_;
                    v___y_2424_ = v___y_2449_;
                    v___y_2425_ = v___y_2450_;
                    v___y_2426_ = v___y_2452_;
                    v___y_2427_ = v___y_2455_;
                    v___y_2428_ = v___y_2453_;
                    v___y_2429_ = v___y_2454_;
                    v___y_2430_ = v___y_2455_;
                    state = 4;
                    continue;
                } else {
                    v_val_2457_ = crate::leanh::lean_ctor_get(v___x_2456_, 0);
                    crate::leanh::lean_inc(v_val_2457_);
                    crate::leanh::lean_dec_ref_known(v___x_2456_, 1);
                    v___y_2423_ = v___y_2448_;
                    v___y_2424_ = v___y_2449_;
                    v___y_2425_ = v___y_2450_;
                    v___y_2426_ = v___y_2452_;
                    v___y_2427_ = v___y_2455_;
                    v___y_2428_ = v___y_2453_;
                    v___y_2429_ = v___y_2454_;
                    v___y_2430_ = v_val_2457_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2466_ = l_Lean_replaceRef(v_ref_2377_, v___y_2460_);
                v___x_2467_ = l_Lean_Syntax_getPos_x3f(v_ref_2466_, v___y_2464_);
                if crate::leanh::lean_obj_tag(v___x_2467_) == 0 {
                    v___x_2468_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2448_ = v___y_2459_;
                    v___y_2449_ = v___y_2465_;
                    v___y_2450_ = v___y_2461_;
                    v___y_2451_ = v_ref_2466_;
                    v___y_2452_ = v___y_2462_;
                    v___y_2453_ = v___y_2463_;
                    v___y_2454_ = v___y_2464_;
                    v___y_2455_ = v___x_2468_;
                    state = 7;
                    continue;
                } else {
                    v_val_2469_ = crate::leanh::lean_ctor_get(v___x_2467_, 0);
                    crate::leanh::lean_inc(v_val_2469_);
                    crate::leanh::lean_dec_ref_known(v___x_2467_, 1);
                    v___y_2448_ = v___y_2459_;
                    v___y_2449_ = v___y_2465_;
                    v___y_2450_ = v___y_2461_;
                    v___y_2451_ = v_ref_2466_;
                    v___y_2452_ = v___y_2462_;
                    v___y_2453_ = v___y_2463_;
                    v___y_2454_ = v___y_2464_;
                    v___y_2455_ = v_val_2469_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2478_ == 0 {
                    v___y_2459_ = v___y_2474_;
                    v___y_2460_ = v___y_2472_;
                    v___y_2461_ = v___y_2473_;
                    v___y_2462_ = v___y_2475_;
                    v___y_2463_ = v___y_2476_;
                    v___y_2464_ = v___y_2477_;
                    v___y_2465_ = v_severity_2379_;
                    state = 8;
                    continue;
                } else {
                    v___y_2459_ = v___y_2474_;
                    v___y_2460_ = v___y_2472_;
                    v___y_2461_ = v___y_2473_;
                    v___y_2462_ = v___y_2475_;
                    v___y_2463_ = v___y_2476_;
                    v___y_2464_ = v___y_2477_;
                    v___y_2465_ = v___x_2470_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2480_ == 0 {
                    v_fileName_2481_ = crate::leanh::lean_ctor_get(v___y_2383_, 0);
                    v_fileMap_2482_ = crate::leanh::lean_ctor_get(v___y_2383_, 1);
                    v_options_2483_ = crate::leanh::lean_ctor_get(v___y_2383_, 2);
                    v_ref_2484_ = crate::leanh::lean_ctor_get(v___y_2383_, 5);
                    v_suppressElabErrors_2485_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_2383_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2486_ = crate::leanh::lean_box((v___y_2480_) as usize);
                    v___x_2487_ = crate::leanh::lean_box((v_suppressElabErrors_2485_) as usize);
                    v___f_2488_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_2488_, 0, v___x_2486_);
                    crate::leanh::lean_closure_set(v___f_2488_, 1, v___x_2487_);
                    v___x_2489_ = 1;
                    v___x_2490_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2379_, v___x_2489_);
                    if v___x_2490_ == 0 {
                        v___y_2472_ = v_ref_2484_;
                        v___y_2473_ = v_fileName_2481_;
                        v___y_2474_ = v___f_2488_;
                        v___y_2475_ = v_suppressElabErrors_2485_;
                        v___y_2476_ = v_fileMap_2482_;
                        v___y_2477_ = v___y_2480_;
                        v___y_2478_ = v___x_2490_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2491_ = l_Lean_warningAsError;
                        v___x_2492_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v_options_2483_, v___x_2491_);
                        v___y_2472_ = v_ref_2484_;
                        v___y_2473_ = v_fileName_2481_;
                        v___y_2474_ = v___f_2488_;
                        v___y_2475_ = v_suppressElabErrors_2485_;
                        v___y_2476_ = v_fileMap_2482_;
                        v___y_2477_ = v___y_2480_;
                        v___y_2478_ = v___x_2492_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_2378_);
                    v___x_2493_ = crate::leanh::lean_box(0);
                    v___x_2494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2494_, 0, v___x_2493_);
                    return v___x_2494_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___boxed(
    mut v_ref_2497_: *mut crate::leanh::LeanObject,
    mut v_msgData_2498_: *mut crate::leanh::LeanObject,
    mut v_severity_2499_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2500_: *mut crate::leanh::LeanObject,
    mut v___y_2501_: *mut crate::leanh::LeanObject,
    mut v___y_2502_: *mut crate::leanh::LeanObject,
    mut v___y_2503_: *mut crate::leanh::LeanObject,
    mut v___y_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2506_: u8 = 0;
    let mut v_isSilent_boxed_2507_: u8 = 0;
    let mut v_res_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2506_ = (crate::leanh::lean_unbox(v_severity_2499_) as u8);
    v_isSilent_boxed_2507_ = (crate::leanh::lean_unbox(v_isSilent_2500_) as u8);
    v_res_2508_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(v_ref_2497_, v_msgData_2498_, v_severity_boxed_2506_, v_isSilent_boxed_2507_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
    crate::leanh::lean_dec(v___y_2504_);
    crate::leanh::lean_dec_ref(v___y_2503_);
    crate::leanh::lean_dec(v___y_2502_);
    crate::leanh::lean_dec_ref(v___y_2501_);
    crate::leanh::lean_dec(v_ref_2497_);
    return v_res_2508_;
}
pub unsafe fn l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4(
    mut v_ref_2509_: *mut crate::leanh::LeanObject,
    mut v_msgData_2510_: *mut crate::leanh::LeanObject,
    mut v___y_2511_: *mut crate::leanh::LeanObject,
    mut v___y_2512_: *mut crate::leanh::LeanObject,
    mut v___y_2513_: *mut crate::leanh::LeanObject,
    mut v___y_2514_: *mut crate::leanh::LeanObject,
    mut v___y_2515_: *mut crate::leanh::LeanObject,
    mut v___y_2516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2518_: u8 = 0;
    let mut v___x_2519_: u8 = 0;
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2518_ = 0;
    v___x_2519_ = 0;
    v___x_2520_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(v_ref_2509_, v_msgData_2510_, v___x_2518_, v___x_2519_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
    return v___x_2520_;
}
pub unsafe fn l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4___boxed(
    mut v_ref_2521_: *mut crate::leanh::LeanObject,
    mut v_msgData_2522_: *mut crate::leanh::LeanObject,
    mut v___y_2523_: *mut crate::leanh::LeanObject,
    mut v___y_2524_: *mut crate::leanh::LeanObject,
    mut v___y_2525_: *mut crate::leanh::LeanObject,
    mut v___y_2526_: *mut crate::leanh::LeanObject,
    mut v___y_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
    mut v___y_2529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2530_ = l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4(
        v_ref_2521_,
        v_msgData_2522_,
        v___y_2523_,
        v___y_2524_,
        v___y_2525_,
        v___y_2526_,
        v___y_2527_,
        v___y_2528_,
    );
    crate::leanh::lean_dec(v___y_2528_);
    crate::leanh::lean_dec_ref(v___y_2527_);
    crate::leanh::lean_dec(v___y_2526_);
    crate::leanh::lean_dec_ref(v___y_2525_);
    crate::leanh::lean_dec(v___y_2524_);
    crate::leanh::lean_dec_ref(v___y_2523_);
    crate::leanh::lean_dec(v_ref_2521_);
    return v_res_2530_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(
    mut v_msgData_2531_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: u8 = 0;
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2544_: u8 = 0;
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2556_: u8 = 0;
    let mut v_unused_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2535_ = crate::leanh::lean_ctor_get(v___y_2533_, 2);
                v___x_2536_ = l_Lean_Elab_pp_macroStack;
                v___x_2537_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v_options_2535_, v___x_2536_);
                if v___x_2537_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_2532_);
                    v___x_2538_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2538_, 0, v_msgData_2531_);
                    return v___x_2538_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_2532_) == 0 {
                        v___x_2539_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2539_, 0, v_msgData_2531_);
                        return v___x_2539_;
                    } else {
                        v_head_2540_ = crate::leanh::lean_ctor_get(v_macroStack_2532_, 0);
                        crate::leanh::lean_inc(v_head_2540_);
                        v_after_2541_ = crate::leanh::lean_ctor_get(v_head_2540_, 1);
                        v_isSharedCheck_2556_ =
                            (!crate::leanh::lean_is_exclusive(v_head_2540_)) as u8;
                        if v_isSharedCheck_2556_ == 0 {
                            v_unused_2557_ = crate::leanh::lean_ctor_get(v_head_2540_, 0);
                            crate::leanh::lean_dec(v_unused_2557_);
                            v___x_2543_ = v_head_2540_;
                            v_isShared_2544_ = v_isSharedCheck_2556_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_2541_);
                            crate::leanh::lean_dec(v_head_2540_);
                            v___x_2543_ = crate::leanh::lean_box(0);
                            v_isShared_2544_ = v_isSharedCheck_2556_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2545_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0);
                if v_isShared_2544_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2543_, 7);
                    crate::leanh::lean_ctor_set(v___x_2543_, 1, v___x_2545_);
                    crate::leanh::lean_ctor_set(v___x_2543_, 0, v_msgData_2531_);
                    v___x_2547_ = v___x_2543_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2555_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_msgData_2531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 1, v___x_2545_);
                    v___x_2547_ = v_reuseFailAlloc_2555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2548_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2);
                v___x_2549_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2549_, 0, v___x_2547_);
                crate::leanh::lean_ctor_set(v___x_2549_, 1, v___x_2548_);
                v___x_2550_ = l_Lean_MessageData_ofSyntax(v_after_2541_);
                v___x_2551_ = l_Lean_indentD(v___x_2550_);
                v_msgData_2552_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_2552_, 0, v___x_2549_);
                crate::leanh::lean_ctor_set(v_msgData_2552_, 1, v___x_2551_);
                v___x_2553_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4(v_msgData_2552_, v_macroStack_2532_);
                v___x_2554_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2554_, 0, v___x_2553_);
                return v___x_2554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg___boxed(
    mut v_msgData_2558_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2559_: *mut crate::leanh::LeanObject,
    mut v___y_2560_: *mut crate::leanh::LeanObject,
    mut v___y_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2562_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(v_msgData_2558_, v_macroStack_2559_, v___y_2560_);
    crate::leanh::lean_dec_ref(v___y_2560_);
    return v_res_2562_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(
    mut v_msg_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: *mut crate::leanh::LeanObject,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
    mut v___y_2567_: *mut crate::leanh::LeanObject,
    mut v___y_2568_: *mut crate::leanh::LeanObject,
    mut v___y_2569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2571_ = crate::leanh::lean_ctor_get(v___y_2568_, 5);
                v___x_2572_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(v_msg_2563_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
                v_a_2573_ = crate::leanh::lean_ctor_get(v___x_2572_, 0);
                crate::leanh::lean_inc(v_a_2573_);
                crate::leanh::lean_dec_ref(v___x_2572_);
                v_macroStack_2574_ = crate::leanh::lean_ctor_get(v___y_2564_, 1);
                v___x_2575_ = l_Lean_Elab_getBetterRef(v_ref_2571_, v_macroStack_2574_);
                crate::leanh::lean_inc(v_macroStack_2574_);
                v___x_2576_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(v_a_2573_, v_macroStack_2574_, v___y_2568_);
                v_a_2577_ = crate::leanh::lean_ctor_get(v___x_2576_, 0);
                v_isSharedCheck_2585_ = (!crate::leanh::lean_is_exclusive(v___x_2576_)) as u8;
                if v_isSharedCheck_2585_ == 0 {
                    v___x_2579_ = v___x_2576_;
                    v_isShared_2580_ = v_isSharedCheck_2585_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2577_);
                    crate::leanh::lean_dec(v___x_2576_);
                    v___x_2579_ = crate::leanh::lean_box(0);
                    v_isShared_2580_ = v_isSharedCheck_2585_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2581_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2581_, 0, v___x_2575_);
                crate::leanh::lean_ctor_set(v___x_2581_, 1, v_a_2577_);
                if v_isShared_2580_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2579_, 1);
                    crate::leanh::lean_ctor_set(v___x_2579_, 0, v___x_2581_);
                    v___x_2583_ = v___x_2579_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
                    v___x_2583_ = v_reuseFailAlloc_2584_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg___boxed(
    mut v_msg_2586_: *mut crate::leanh::LeanObject,
    mut v___y_2587_: *mut crate::leanh::LeanObject,
    mut v___y_2588_: *mut crate::leanh::LeanObject,
    mut v___y_2589_: *mut crate::leanh::LeanObject,
    mut v___y_2590_: *mut crate::leanh::LeanObject,
    mut v___y_2591_: *mut crate::leanh::LeanObject,
    mut v___y_2592_: *mut crate::leanh::LeanObject,
    mut v___y_2593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2594_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(v_msg_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
    crate::leanh::lean_dec(v___y_2592_);
    crate::leanh::lean_dec_ref(v___y_2591_);
    crate::leanh::lean_dec(v___y_2590_);
    crate::leanh::lean_dec_ref(v___y_2589_);
    crate::leanh::lean_dec(v___y_2588_);
    crate::leanh::lean_dec_ref(v___y_2587_);
    return v_res_2594_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(
    mut v_ref_2595_: *mut crate::leanh::LeanObject,
    mut v_msg_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
    mut v___y_2598_: *mut crate::leanh::LeanObject,
    mut v___y_2599_: *mut crate::leanh::LeanObject,
    mut v___y_2600_: *mut crate::leanh::LeanObject,
    mut v___y_2601_: *mut crate::leanh::LeanObject,
    mut v___y_2602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2616_: u8 = 0;
    let mut v_cancelTk_x3f_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2618_: u8 = 0;
    let mut v_inheritedTraceOptions_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2604_ = crate::leanh::lean_ctor_get(v___y_2601_, 0);
    v_fileMap_2605_ = crate::leanh::lean_ctor_get(v___y_2601_, 1);
    v_options_2606_ = crate::leanh::lean_ctor_get(v___y_2601_, 2);
    v_currRecDepth_2607_ = crate::leanh::lean_ctor_get(v___y_2601_, 3);
    v_maxRecDepth_2608_ = crate::leanh::lean_ctor_get(v___y_2601_, 4);
    v_ref_2609_ = crate::leanh::lean_ctor_get(v___y_2601_, 5);
    v_currNamespace_2610_ = crate::leanh::lean_ctor_get(v___y_2601_, 6);
    v_openDecls_2611_ = crate::leanh::lean_ctor_get(v___y_2601_, 7);
    v_initHeartbeats_2612_ = crate::leanh::lean_ctor_get(v___y_2601_, 8);
    v_maxHeartbeats_2613_ = crate::leanh::lean_ctor_get(v___y_2601_, 9);
    v_quotContext_2614_ = crate::leanh::lean_ctor_get(v___y_2601_, 10);
    v_currMacroScope_2615_ = crate::leanh::lean_ctor_get(v___y_2601_, 11);
    v_diag_2616_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2601_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2617_ = crate::leanh::lean_ctor_get(v___y_2601_, 12);
    v_suppressElabErrors_2618_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2601_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2619_ = crate::leanh::lean_ctor_get(v___y_2601_, 13);
    v_ref_2620_ = l_Lean_replaceRef(v_ref_2595_, v_ref_2609_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2619_);
    crate::leanh::lean_inc(v_cancelTk_x3f_2617_);
    crate::leanh::lean_inc(v_currMacroScope_2615_);
    crate::leanh::lean_inc(v_quotContext_2614_);
    crate::leanh::lean_inc(v_maxHeartbeats_2613_);
    crate::leanh::lean_inc(v_initHeartbeats_2612_);
    crate::leanh::lean_inc(v_openDecls_2611_);
    crate::leanh::lean_inc(v_currNamespace_2610_);
    crate::leanh::lean_inc(v_maxRecDepth_2608_);
    crate::leanh::lean_inc(v_currRecDepth_2607_);
    crate::leanh::lean_inc_ref(v_options_2606_);
    crate::leanh::lean_inc_ref(v_fileMap_2605_);
    crate::leanh::lean_inc_ref(v_fileName_2604_);
    v___x_2621_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2621_, 0, v_fileName_2604_);
    crate::leanh::lean_ctor_set(v___x_2621_, 1, v_fileMap_2605_);
    crate::leanh::lean_ctor_set(v___x_2621_, 2, v_options_2606_);
    crate::leanh::lean_ctor_set(v___x_2621_, 3, v_currRecDepth_2607_);
    crate::leanh::lean_ctor_set(v___x_2621_, 4, v_maxRecDepth_2608_);
    crate::leanh::lean_ctor_set(v___x_2621_, 5, v_ref_2620_);
    crate::leanh::lean_ctor_set(v___x_2621_, 6, v_currNamespace_2610_);
    crate::leanh::lean_ctor_set(v___x_2621_, 7, v_openDecls_2611_);
    crate::leanh::lean_ctor_set(v___x_2621_, 8, v_initHeartbeats_2612_);
    crate::leanh::lean_ctor_set(v___x_2621_, 9, v_maxHeartbeats_2613_);
    crate::leanh::lean_ctor_set(v___x_2621_, 10, v_quotContext_2614_);
    crate::leanh::lean_ctor_set(v___x_2621_, 11, v_currMacroScope_2615_);
    crate::leanh::lean_ctor_set(v___x_2621_, 12, v_cancelTk_x3f_2617_);
    crate::leanh::lean_ctor_set(v___x_2621_, 13, v_inheritedTraceOptions_2619_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2621_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_2616_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2621_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2618_,
    );
    v___x_2622_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(v_msg_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___x_2621_, v___y_2602_);
    crate::leanh::lean_dec_ref_known(v___x_2621_, 14);
    return v___x_2622_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg___boxed(
    mut v_ref_2623_: *mut crate::leanh::LeanObject,
    mut v_msg_2624_: *mut crate::leanh::LeanObject,
    mut v___y_2625_: *mut crate::leanh::LeanObject,
    mut v___y_2626_: *mut crate::leanh::LeanObject,
    mut v___y_2627_: *mut crate::leanh::LeanObject,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
    mut v___y_2629_: *mut crate::leanh::LeanObject,
    mut v___y_2630_: *mut crate::leanh::LeanObject,
    mut v___y_2631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2632_ =
        l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(
            v_ref_2623_,
            v_msg_2624_,
            v___y_2625_,
            v___y_2626_,
            v___y_2627_,
            v___y_2628_,
            v___y_2629_,
            v___y_2630_,
        );
    crate::leanh::lean_dec(v___y_2630_);
    crate::leanh::lean_dec_ref(v___y_2629_);
    crate::leanh::lean_dec(v___y_2628_);
    crate::leanh::lean_dec_ref(v___y_2627_);
    crate::leanh::lean_dec(v___y_2626_);
    crate::leanh::lean_dec_ref(v___y_2625_);
    crate::leanh::lean_dec(v_ref_2623_);
    return v_res_2632_;
}
pub unsafe fn l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__4(
    mut v_msg_2633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2634_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___closed__0;
    v___x_2635_ = lean_panic_fn_borrowed(v___x_2634_, v_msg_2633_);
    return v___x_2635_;
}
pub unsafe fn l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(
    mut v_val_2636_: *mut crate::leanh::LeanObject,
    mut v___x_2637_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2640_ = lean_get_set_stderr(v_val_2636_);
    crate::leanh::lean_dec_ref(v___x_2640_);
    v___x_2641_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2641_, 0, v___x_2637_);
    return v___x_2641_;
}
pub unsafe fn l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0___boxed(
    mut v_val_2642_: *mut crate::leanh::LeanObject,
    mut v___x_2643_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2644_: *mut crate::leanh::LeanObject,
    mut v___y_2645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2646_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(v_val_2642_, v___x_2643_, v_a_x3f_2644_);
    crate::leanh::lean_dec(v_a_x3f_2644_);
    return v_res_2646_;
}
pub unsafe fn l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg(
    mut v_h_2647_: *mut crate::leanh::LeanObject,
    mut v_x_2648_: *mut crate::leanh::LeanObject,
    mut v___y_2649_: *mut crate::leanh::LeanObject,
    mut v___y_2650_: *mut crate::leanh::LeanObject,
    mut v___y_2651_: *mut crate::leanh::LeanObject,
    mut v___y_2652_: *mut crate::leanh::LeanObject,
    mut v___y_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut v_unused_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2675_: u8 = 0;
    let mut v_a_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2685_: u8 = 0;
    let mut v_unused_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2656_ = lean_get_set_stderr(v_h_2647_);
                v___x_2657_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_2654_);
                crate::leanh::lean_inc_ref(v___y_2653_);
                crate::leanh::lean_inc(v___y_2652_);
                crate::leanh::lean_inc_ref(v___y_2651_);
                crate::leanh::lean_inc(v___y_2650_);
                crate::leanh::lean_inc_ref(v___y_2649_);
                v_r_2658_ = crate::leanh::lean_apply_7(
                    v_x_2648_,
                    v___y_2649_,
                    v___y_2650_,
                    v___y_2651_,
                    v___y_2652_,
                    v___y_2653_,
                    v___y_2654_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_2658_) == 0 {
                    v_a_2659_ = crate::leanh::lean_ctor_get(v_r_2658_, 0);
                    v_isSharedCheck_2675_ = (!crate::leanh::lean_is_exclusive(v_r_2658_)) as u8;
                    if v_isSharedCheck_2675_ == 0 {
                        v___x_2661_ = v_r_2658_;
                        v_isShared_2662_ = v_isSharedCheck_2675_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2659_);
                        crate::leanh::lean_dec(v_r_2658_);
                        v___x_2661_ = crate::leanh::lean_box(0);
                        v_isShared_2662_ = v_isSharedCheck_2675_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2676_ = crate::leanh::lean_ctor_get(v_r_2658_, 0);
                    crate::leanh::lean_inc(v_a_2676_);
                    crate::leanh::lean_dec_ref_known(v_r_2658_, 1);
                    v___x_2677_ = crate::leanh::lean_box(0);
                    v___x_2678_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(v___x_2656_, v___x_2657_, v___x_2677_);
                    v_isSharedCheck_2685_ = (!crate::leanh::lean_is_exclusive(v___x_2678_)) as u8;
                    if v_isSharedCheck_2685_ == 0 {
                        v_unused_2686_ = crate::leanh::lean_ctor_get(v___x_2678_, 0);
                        crate::leanh::lean_dec(v_unused_2686_);
                        v___x_2680_ = v___x_2678_;
                        v_isShared_2681_ = v_isSharedCheck_2685_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2678_);
                        v___x_2680_ = crate::leanh::lean_box(0);
                        v_isShared_2681_ = v_isSharedCheck_2685_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_2659_);
                if v_isShared_2662_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2661_, 1);
                    v___x_2664_ = v___x_2661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2674_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2659_);
                    v___x_2664_ = v_reuseFailAlloc_2674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2665_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(v___x_2656_, v___x_2657_, v___x_2664_);
                crate::leanh::lean_dec_ref(v___x_2664_);
                v_isSharedCheck_2672_ = (!crate::leanh::lean_is_exclusive(v___x_2665_)) as u8;
                if v_isSharedCheck_2672_ == 0 {
                    v_unused_2673_ = crate::leanh::lean_ctor_get(v___x_2665_, 0);
                    crate::leanh::lean_dec(v_unused_2673_);
                    v___x_2667_ = v___x_2665_;
                    v_isShared_2668_ = v_isSharedCheck_2672_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2665_);
                    v___x_2667_ = crate::leanh::lean_box(0);
                    v_isShared_2668_ = v_isSharedCheck_2672_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2668_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2667_, 0, v_a_2659_);
                    v___x_2670_ = v___x_2667_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2671_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2659_);
                    v___x_2670_ = v_reuseFailAlloc_2671_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2670_;
            }
            5 => {
                if v_isShared_2681_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2680_, 1);
                    crate::leanh::lean_ctor_set(v___x_2680_, 0, v_a_2676_);
                    v___x_2683_ = v___x_2680_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2684_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2676_);
                    v___x_2683_ = v_reuseFailAlloc_2684_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___boxed(
    mut v_h_2687_: *mut crate::leanh::LeanObject,
    mut v_x_2688_: *mut crate::leanh::LeanObject,
    mut v___y_2689_: *mut crate::leanh::LeanObject,
    mut v___y_2690_: *mut crate::leanh::LeanObject,
    mut v___y_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
    mut v___y_2693_: *mut crate::leanh::LeanObject,
    mut v___y_2694_: *mut crate::leanh::LeanObject,
    mut v___y_2695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2696_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg(v_h_2687_, v_x_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
    crate::leanh::lean_dec(v___y_2694_);
    crate::leanh::lean_dec_ref(v___y_2693_);
    crate::leanh::lean_dec(v___y_2692_);
    crate::leanh::lean_dec_ref(v___y_2691_);
    crate::leanh::lean_dec(v___y_2690_);
    crate::leanh::lean_dec_ref(v___y_2689_);
    return v_res_2696_;
}
pub unsafe fn l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5(
    mut v_00_u03b1_2697_: *mut crate::leanh::LeanObject,
    mut v_h_2698_: *mut crate::leanh::LeanObject,
    mut v_x_2699_: *mut crate::leanh::LeanObject,
    mut v___y_2700_: *mut crate::leanh::LeanObject,
    mut v___y_2701_: *mut crate::leanh::LeanObject,
    mut v___y_2702_: *mut crate::leanh::LeanObject,
    mut v___y_2703_: *mut crate::leanh::LeanObject,
    mut v___y_2704_: *mut crate::leanh::LeanObject,
    mut v___y_2705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2707_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg(v_h_2698_, v_x_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
    return v___x_2707_;
}
pub unsafe fn l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___boxed(
    mut v_00_u03b1_2708_: *mut crate::leanh::LeanObject,
    mut v_h_2709_: *mut crate::leanh::LeanObject,
    mut v_x_2710_: *mut crate::leanh::LeanObject,
    mut v___y_2711_: *mut crate::leanh::LeanObject,
    mut v___y_2712_: *mut crate::leanh::LeanObject,
    mut v___y_2713_: *mut crate::leanh::LeanObject,
    mut v___y_2714_: *mut crate::leanh::LeanObject,
    mut v___y_2715_: *mut crate::leanh::LeanObject,
    mut v___y_2716_: *mut crate::leanh::LeanObject,
    mut v___y_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5(v_00_u03b1_2708_, v_h_2709_, v_x_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
    crate::leanh::lean_dec(v___y_2716_);
    crate::leanh::lean_dec_ref(v___y_2715_);
    crate::leanh::lean_dec(v___y_2714_);
    crate::leanh::lean_dec_ref(v___y_2713_);
    crate::leanh::lean_dec(v___y_2712_);
    crate::leanh::lean_dec_ref(v___y_2711_);
    return v_res_2718_;
}
pub unsafe fn l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(
    mut v_val_2719_: *mut crate::leanh::LeanObject,
    mut v___x_2720_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = lean_get_set_stdin(v_val_2719_);
    crate::leanh::lean_dec_ref(v___x_2723_);
    v___x_2724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2724_, 0, v___x_2720_);
    return v___x_2724_;
}
pub unsafe fn l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0___boxed(
    mut v_val_2725_: *mut crate::leanh::LeanObject,
    mut v___x_2726_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2727_: *mut crate::leanh::LeanObject,
    mut v___y_2728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2729_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(v_val_2725_, v___x_2726_, v_a_x3f_2727_);
    crate::leanh::lean_dec(v_a_x3f_2727_);
    return v_res_2729_;
}
pub unsafe fn l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(
    mut v_h_2730_: *mut crate::leanh::LeanObject,
    mut v_x_2731_: *mut crate::leanh::LeanObject,
    mut v___y_2732_: *mut crate::leanh::LeanObject,
    mut v___y_2733_: *mut crate::leanh::LeanObject,
    mut v___y_2734_: *mut crate::leanh::LeanObject,
    mut v___y_2735_: *mut crate::leanh::LeanObject,
    mut v___y_2736_: *mut crate::leanh::LeanObject,
    mut v___y_2737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2745_: u8 = 0;
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2751_: u8 = 0;
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2755_: u8 = 0;
    let mut v_unused_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2758_: u8 = 0;
    let mut v_a_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2764_: u8 = 0;
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2768_: u8 = 0;
    let mut v_unused_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2739_ = lean_get_set_stdin(v_h_2730_);
                v___x_2740_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_2737_);
                crate::leanh::lean_inc_ref(v___y_2736_);
                crate::leanh::lean_inc(v___y_2735_);
                crate::leanh::lean_inc_ref(v___y_2734_);
                crate::leanh::lean_inc(v___y_2733_);
                crate::leanh::lean_inc_ref(v___y_2732_);
                v_r_2741_ = crate::leanh::lean_apply_7(
                    v_x_2731_,
                    v___y_2732_,
                    v___y_2733_,
                    v___y_2734_,
                    v___y_2735_,
                    v___y_2736_,
                    v___y_2737_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_2741_) == 0 {
                    v_a_2742_ = crate::leanh::lean_ctor_get(v_r_2741_, 0);
                    v_isSharedCheck_2758_ = (!crate::leanh::lean_is_exclusive(v_r_2741_)) as u8;
                    if v_isSharedCheck_2758_ == 0 {
                        v___x_2744_ = v_r_2741_;
                        v_isShared_2745_ = v_isSharedCheck_2758_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2742_);
                        crate::leanh::lean_dec(v_r_2741_);
                        v___x_2744_ = crate::leanh::lean_box(0);
                        v_isShared_2745_ = v_isSharedCheck_2758_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2759_ = crate::leanh::lean_ctor_get(v_r_2741_, 0);
                    crate::leanh::lean_inc(v_a_2759_);
                    crate::leanh::lean_dec_ref_known(v_r_2741_, 1);
                    v___x_2760_ = crate::leanh::lean_box(0);
                    v___x_2761_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(v___x_2739_, v___x_2740_, v___x_2760_);
                    v_isSharedCheck_2768_ = (!crate::leanh::lean_is_exclusive(v___x_2761_)) as u8;
                    if v_isSharedCheck_2768_ == 0 {
                        v_unused_2769_ = crate::leanh::lean_ctor_get(v___x_2761_, 0);
                        crate::leanh::lean_dec(v_unused_2769_);
                        v___x_2763_ = v___x_2761_;
                        v_isShared_2764_ = v_isSharedCheck_2768_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2761_);
                        v___x_2763_ = crate::leanh::lean_box(0);
                        v_isShared_2764_ = v_isSharedCheck_2768_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_2742_);
                if v_isShared_2745_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2744_, 1);
                    v___x_2747_ = v___x_2744_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2757_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2742_);
                    v___x_2747_ = v_reuseFailAlloc_2757_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2748_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(v___x_2739_, v___x_2740_, v___x_2747_);
                crate::leanh::lean_dec_ref(v___x_2747_);
                v_isSharedCheck_2755_ = (!crate::leanh::lean_is_exclusive(v___x_2748_)) as u8;
                if v_isSharedCheck_2755_ == 0 {
                    v_unused_2756_ = crate::leanh::lean_ctor_get(v___x_2748_, 0);
                    crate::leanh::lean_dec(v_unused_2756_);
                    v___x_2750_ = v___x_2748_;
                    v_isShared_2751_ = v_isSharedCheck_2755_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2748_);
                    v___x_2750_ = crate::leanh::lean_box(0);
                    v_isShared_2751_ = v_isSharedCheck_2755_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2751_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2750_, 0, v_a_2742_);
                    v___x_2753_ = v___x_2750_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2754_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2742_);
                    v___x_2753_ = v_reuseFailAlloc_2754_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2753_;
            }
            5 => {
                if v_isShared_2764_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2763_, 1);
                    crate::leanh::lean_ctor_set(v___x_2763_, 0, v_a_2759_);
                    v___x_2766_ = v___x_2763_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2759_);
                    v___x_2766_ = v_reuseFailAlloc_2767_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___boxed(
    mut v_h_2770_: *mut crate::leanh::LeanObject,
    mut v_x_2771_: *mut crate::leanh::LeanObject,
    mut v___y_2772_: *mut crate::leanh::LeanObject,
    mut v___y_2773_: *mut crate::leanh::LeanObject,
    mut v___y_2774_: *mut crate::leanh::LeanObject,
    mut v___y_2775_: *mut crate::leanh::LeanObject,
    mut v___y_2776_: *mut crate::leanh::LeanObject,
    mut v___y_2777_: *mut crate::leanh::LeanObject,
    mut v___y_2778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2779_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(v_h_2770_, v_x_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
    crate::leanh::lean_dec(v___y_2777_);
    crate::leanh::lean_dec_ref(v___y_2776_);
    crate::leanh::lean_dec(v___y_2775_);
    crate::leanh::lean_dec_ref(v___y_2774_);
    crate::leanh::lean_dec(v___y_2773_);
    crate::leanh::lean_dec_ref(v___y_2772_);
    return v_res_2779_;
}
pub unsafe fn l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(
    mut v_val_2780_: *mut crate::leanh::LeanObject,
    mut v___x_2781_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2784_ = lean_get_set_stdout(v_val_2780_);
    crate::leanh::lean_dec_ref(v___x_2784_);
    v___x_2785_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_2781_);
    return v___x_2785_;
}
pub unsafe fn l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0___boxed(
    mut v_val_2786_: *mut crate::leanh::LeanObject,
    mut v___x_2787_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2788_: *mut crate::leanh::LeanObject,
    mut v___y_2789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2790_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(v_val_2786_, v___x_2787_, v_a_x3f_2788_);
    crate::leanh::lean_dec(v_a_x3f_2788_);
    return v_res_2790_;
}
pub unsafe fn l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg(
    mut v_h_2791_: *mut crate::leanh::LeanObject,
    mut v_x_2792_: *mut crate::leanh::LeanObject,
    mut v___y_2793_: *mut crate::leanh::LeanObject,
    mut v___y_2794_: *mut crate::leanh::LeanObject,
    mut v___y_2795_: *mut crate::leanh::LeanObject,
    mut v___y_2796_: *mut crate::leanh::LeanObject,
    mut v___y_2797_: *mut crate::leanh::LeanObject,
    mut v___y_2798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2806_: u8 = 0;
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v_unused_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2819_: u8 = 0;
    let mut v_a_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2829_: u8 = 0;
    let mut v_unused_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2800_ = lean_get_set_stdout(v_h_2791_);
                v___x_2801_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_2798_);
                crate::leanh::lean_inc_ref(v___y_2797_);
                crate::leanh::lean_inc(v___y_2796_);
                crate::leanh::lean_inc_ref(v___y_2795_);
                crate::leanh::lean_inc(v___y_2794_);
                crate::leanh::lean_inc_ref(v___y_2793_);
                v_r_2802_ = crate::leanh::lean_apply_7(
                    v_x_2792_,
                    v___y_2793_,
                    v___y_2794_,
                    v___y_2795_,
                    v___y_2796_,
                    v___y_2797_,
                    v___y_2798_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_2802_) == 0 {
                    v_a_2803_ = crate::leanh::lean_ctor_get(v_r_2802_, 0);
                    v_isSharedCheck_2819_ = (!crate::leanh::lean_is_exclusive(v_r_2802_)) as u8;
                    if v_isSharedCheck_2819_ == 0 {
                        v___x_2805_ = v_r_2802_;
                        v_isShared_2806_ = v_isSharedCheck_2819_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2803_);
                        crate::leanh::lean_dec(v_r_2802_);
                        v___x_2805_ = crate::leanh::lean_box(0);
                        v_isShared_2806_ = v_isSharedCheck_2819_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2820_ = crate::leanh::lean_ctor_get(v_r_2802_, 0);
                    crate::leanh::lean_inc(v_a_2820_);
                    crate::leanh::lean_dec_ref_known(v_r_2802_, 1);
                    v___x_2821_ = crate::leanh::lean_box(0);
                    v___x_2822_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(v___x_2800_, v___x_2801_, v___x_2821_);
                    v_isSharedCheck_2829_ = (!crate::leanh::lean_is_exclusive(v___x_2822_)) as u8;
                    if v_isSharedCheck_2829_ == 0 {
                        v_unused_2830_ = crate::leanh::lean_ctor_get(v___x_2822_, 0);
                        crate::leanh::lean_dec(v_unused_2830_);
                        v___x_2824_ = v___x_2822_;
                        v_isShared_2825_ = v_isSharedCheck_2829_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2822_);
                        v___x_2824_ = crate::leanh::lean_box(0);
                        v_isShared_2825_ = v_isSharedCheck_2829_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_2803_);
                if v_isShared_2806_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2805_, 1);
                    v___x_2808_ = v___x_2805_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2818_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2803_);
                    v___x_2808_ = v_reuseFailAlloc_2818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2809_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(v___x_2800_, v___x_2801_, v___x_2808_);
                crate::leanh::lean_dec_ref(v___x_2808_);
                v_isSharedCheck_2816_ = (!crate::leanh::lean_is_exclusive(v___x_2809_)) as u8;
                if v_isSharedCheck_2816_ == 0 {
                    v_unused_2817_ = crate::leanh::lean_ctor_get(v___x_2809_, 0);
                    crate::leanh::lean_dec(v_unused_2817_);
                    v___x_2811_ = v___x_2809_;
                    v_isShared_2812_ = v_isSharedCheck_2816_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2809_);
                    v___x_2811_ = crate::leanh::lean_box(0);
                    v_isShared_2812_ = v_isSharedCheck_2816_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2812_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2811_, 0, v_a_2803_);
                    v___x_2814_ = v___x_2811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2803_);
                    v___x_2814_ = v_reuseFailAlloc_2815_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2814_;
            }
            5 => {
                if v_isShared_2825_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2824_, 1);
                    crate::leanh::lean_ctor_set(v___x_2824_, 0, v_a_2820_);
                    v___x_2827_ = v___x_2824_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2828_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2820_);
                    v___x_2827_ = v_reuseFailAlloc_2828_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___boxed(
    mut v_h_2831_: *mut crate::leanh::LeanObject,
    mut v_x_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
    mut v___y_2837_: *mut crate::leanh::LeanObject,
    mut v___y_2838_: *mut crate::leanh::LeanObject,
    mut v___y_2839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2840_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg(v_h_2831_, v_x_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
    crate::leanh::lean_dec(v___y_2838_);
    crate::leanh::lean_dec_ref(v___y_2837_);
    crate::leanh::lean_dec(v___y_2836_);
    crate::leanh::lean_dec_ref(v___y_2835_);
    crate::leanh::lean_dec(v___y_2834_);
    crate::leanh::lean_dec_ref(v___y_2833_);
    return v_res_2840_;
}
pub unsafe fn l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2(
    mut v_00_u03b1_2841_: *mut crate::leanh::LeanObject,
    mut v_h_2842_: *mut crate::leanh::LeanObject,
    mut v_x_2843_: *mut crate::leanh::LeanObject,
    mut v___y_2844_: *mut crate::leanh::LeanObject,
    mut v___y_2845_: *mut crate::leanh::LeanObject,
    mut v___y_2846_: *mut crate::leanh::LeanObject,
    mut v___y_2847_: *mut crate::leanh::LeanObject,
    mut v___y_2848_: *mut crate::leanh::LeanObject,
    mut v___y_2849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2851_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg(v_h_2842_, v_x_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
    return v___x_2851_;
}
pub unsafe fn l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___boxed(
    mut v_00_u03b1_2852_: *mut crate::leanh::LeanObject,
    mut v_h_2853_: *mut crate::leanh::LeanObject,
    mut v_x_2854_: *mut crate::leanh::LeanObject,
    mut v___y_2855_: *mut crate::leanh::LeanObject,
    mut v___y_2856_: *mut crate::leanh::LeanObject,
    mut v___y_2857_: *mut crate::leanh::LeanObject,
    mut v___y_2858_: *mut crate::leanh::LeanObject,
    mut v___y_2859_: *mut crate::leanh::LeanObject,
    mut v___y_2860_: *mut crate::leanh::LeanObject,
    mut v___y_2861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2862_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2(v_00_u03b1_2852_, v_h_2853_, v_x_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
    crate::leanh::lean_dec(v___y_2860_);
    crate::leanh::lean_dec_ref(v___y_2859_);
    crate::leanh::lean_dec(v___y_2858_);
    crate::leanh::lean_dec_ref(v___y_2857_);
    crate::leanh::lean_dec(v___y_2856_);
    crate::leanh::lean_dec_ref(v___y_2855_);
    return v_res_2862_;
}
pub unsafe fn _init_l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2863_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2864_ = l_ByteArray_empty;
    v___x_2865_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2865_, 0, v___x_2864_);
    crate::leanh::lean_ctor_set(v___x_2865_, 1, v___x_2863_);
    return v___x_2865_;
}
pub unsafe fn _init_l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2869_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__3;
    v___x_2870_ = crate::leanh::lean_unsigned_to_nat(46);
    v___x_2871_ = crate::leanh::lean_unsigned_to_nat(193);
    v___x_2872_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__2;
    v___x_2873_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__1;
    v___x_2874_ = l_mkPanicMessageWithDecl(
        v___x_2873_,
        v___x_2872_,
        v___x_2871_,
        v___x_2870_,
        v___x_2869_,
    );
    return v___x_2874_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(
    mut v_x_2875_: *mut crate::leanh::LeanObject,
    mut v_isolateStderr_2876_: u8,
    mut v___y_2877_: *mut crate::leanh::LeanObject,
    mut v___y_2878_: *mut crate::leanh::LeanObject,
    mut v___y_2879_: *mut crate::leanh::LeanObject,
    mut v___y_2880_: *mut crate::leanh::LeanObject,
    mut v___y_2881_: *mut crate::leanh::LeanObject,
    mut v___y_2882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: u8 = 0;
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2908_: u8 = 0;
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2912_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2889_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0_once), _init_l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0);
                v___x_2890_ = lean_st_mk_ref(v___x_2889_);
                v___x_2891_ = lean_st_mk_ref(v___x_2889_);
                v___x_2892_ = l_IO_FS_Stream_ofBuffer(v___x_2890_);
                crate::leanh::lean_inc(v___x_2891_);
                v___x_2893_ = l_IO_FS_Stream_ofBuffer(v___x_2891_);
                if v_isolateStderr_2876_ == 0 {
                    v___y_2895_ = v_x_2875_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v___x_2893_);
                    v___x_2913_ = crate::leanh::lean_alloc_closure(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___boxed as *mut core::ffi::c_void, 10, 3);
                    crate::leanh::lean_closure_set(v___x_2913_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_2913_, 1, v___x_2893_);
                    crate::leanh::lean_closure_set(v___x_2913_, 2, v_x_2875_);
                    v___y_2895_ = v___x_2913_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2887_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2887_, 0, v___y_2886_);
                crate::leanh::lean_ctor_set(v___x_2887_, 1, v___y_2885_);
                v___x_2888_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2888_, 0, v___x_2887_);
                return v___x_2888_;
            }
            2 => {
                v___x_2896_ = crate::leanh::lean_alloc_closure(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___boxed as *mut core::ffi::c_void, 10, 3);
                crate::leanh::lean_closure_set(v___x_2896_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2896_, 1, v___x_2893_);
                crate::leanh::lean_closure_set(v___x_2896_, 2, v___y_2895_);
                v___x_2897_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(v___x_2892_, v___x_2896_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
                if crate::leanh::lean_obj_tag(v___x_2897_) == 0 {
                    v_a_2898_ = crate::leanh::lean_ctor_get(v___x_2897_, 0);
                    crate::leanh::lean_inc(v_a_2898_);
                    crate::leanh::lean_dec_ref_known(v___x_2897_, 1);
                    v___x_2899_ = lean_st_ref_get(v___x_2891_);
                    crate::leanh::lean_dec(v___x_2891_);
                    v_data_2900_ = crate::leanh::lean_ctor_get(v___x_2899_, 0);
                    crate::leanh::lean_inc_ref(v_data_2900_);
                    crate::leanh::lean_dec(v___x_2899_);
                    v___x_2901_ = lean_string_validate_utf8(v_data_2900_);
                    if v___x_2901_ == 0 {
                        crate::leanh::lean_dec_ref(v_data_2900_);
                        v___x_2902_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4_once), _init_l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4);
                        v___x_2903_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__4(v___x_2902_);
                        v___y_2885_ = v_a_2898_;
                        v___y_2886_ = v___x_2903_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2904_ = lean_string_from_utf8_unchecked(v_data_2900_);
                        v___y_2885_ = v_a_2898_;
                        v___y_2886_ = v___x_2904_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2891_);
                    v_a_2905_ = crate::leanh::lean_ctor_get(v___x_2897_, 0);
                    v_isSharedCheck_2912_ = (!crate::leanh::lean_is_exclusive(v___x_2897_)) as u8;
                    if v_isSharedCheck_2912_ == 0 {
                        v___x_2907_ = v___x_2897_;
                        v_isShared_2908_ = v_isSharedCheck_2912_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2905_);
                        crate::leanh::lean_dec(v___x_2897_);
                        v___x_2907_ = crate::leanh::lean_box(0);
                        v_isShared_2908_ = v_isSharedCheck_2912_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2908_ == 0 {
                    v___x_2910_ = v___x_2907_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
                    v___x_2910_ = v_reuseFailAlloc_2911_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___boxed(
    mut v_x_2914_: *mut crate::leanh::LeanObject,
    mut v_isolateStderr_2915_: *mut crate::leanh::LeanObject,
    mut v___y_2916_: *mut crate::leanh::LeanObject,
    mut v___y_2917_: *mut crate::leanh::LeanObject,
    mut v___y_2918_: *mut crate::leanh::LeanObject,
    mut v___y_2919_: *mut crate::leanh::LeanObject,
    mut v___y_2920_: *mut crate::leanh::LeanObject,
    mut v___y_2921_: *mut crate::leanh::LeanObject,
    mut v___y_2922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isolateStderr_boxed_2923_: u8 = 0;
    let mut v_res_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isolateStderr_boxed_2923_ = (crate::leanh::lean_unbox(v_isolateStderr_2915_) as u8);
    v_res_2924_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(v_x_2914_, v_isolateStderr_boxed_2923_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
    crate::leanh::lean_dec(v___y_2921_);
    crate::leanh::lean_dec_ref(v___y_2920_);
    crate::leanh::lean_dec(v___y_2919_);
    crate::leanh::lean_dec_ref(v___y_2918_);
    crate::leanh::lean_dec(v___y_2917_);
    crate::leanh::lean_dec_ref(v___y_2916_);
    return v_res_2924_;
}
pub unsafe fn _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2930_ = crate::leanh::lean_box(0);
    v___x_2931_ = l_Lean_Level_succ___override(v___x_2930_);
    return v___x_2931_;
}
pub unsafe fn _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2932_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2),
        core::ptr::addr_of_mut!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2_once),
        _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2,
    );
    v___x_2933_ = l_Lean_mkSort(v___x_2932_);
    return v___x_2933_;
}
pub unsafe fn _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2934_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3),
        core::ptr::addr_of_mut!(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3_once),
        _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3,
    );
    v___x_2935_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2935_, 0, v___x_2934_);
    return v___x_2935_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO(
    mut v_stx_2949_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_2950_: *mut crate::leanh::LeanObject,
    mut v_a_2951_: *mut crate::leanh::LeanObject,
    mut v_a_2952_: *mut crate::leanh::LeanObject,
    mut v_a_2953_: *mut crate::leanh::LeanObject,
    mut v_a_2954_: *mut crate::leanh::LeanObject,
    mut v_a_2955_: *mut crate::leanh::LeanObject,
    mut v_a_2956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: u8 = 0;
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2973_: u8 = 0;
    let mut v_cancelTk_x3f_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2975_: u8 = 0;
    let mut v_inheritedTraceOptions_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: u8 = 0;
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2988_: u8 = 0;
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3002_: u8 = 0;
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3009_: u8 = 0;
    let mut v_a_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3029_: u8 = 0;
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: u8 = 0;
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3046_: u8 = 0;
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_reuseFailAlloc_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3055_: u8 = 0;
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3059_: u8 = 0;
    let mut v_a_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3063_: u8 = 0;
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3067_: u8 = 0;
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: u8 = 0;
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: u8 = 0;
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3095_: u8 = 0;
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut v_a_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3103_: u8 = 0;
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3107_: u8 = 0;
    let mut v_a_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3111_: u8 = 0;
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3115_: u8 = 0;
    let mut v_a_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3119_: u8 = 0;
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3123_: u8 = 0;
    let mut v_val_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2958_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1;
                crate::leanh::lean_inc(v_stx_2949_);
                v___x_2959_ = l_Lean_Syntax_isOfKind(v_stx_2949_, v___x_2958_);
                if v___x_2959_ == 0 {
                    crate::leanh::lean_dec(v_expectedType_x3f_2950_);
                    crate::leanh::lean_dec(v_stx_2949_);
                    v___x_2960_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg();
                    return v___x_2960_;
                } else {
                    v_fileName_2961_ = crate::leanh::lean_ctor_get(v_a_2955_, 0);
                    v_fileMap_2962_ = crate::leanh::lean_ctor_get(v_a_2955_, 1);
                    v_options_2963_ = crate::leanh::lean_ctor_get(v_a_2955_, 2);
                    v_currRecDepth_2964_ = crate::leanh::lean_ctor_get(v_a_2955_, 3);
                    v_maxRecDepth_2965_ = crate::leanh::lean_ctor_get(v_a_2955_, 4);
                    v_ref_2966_ = crate::leanh::lean_ctor_get(v_a_2955_, 5);
                    v_currNamespace_2967_ = crate::leanh::lean_ctor_get(v_a_2955_, 6);
                    v_openDecls_2968_ = crate::leanh::lean_ctor_get(v_a_2955_, 7);
                    v_initHeartbeats_2969_ = crate::leanh::lean_ctor_get(v_a_2955_, 8);
                    v_maxHeartbeats_2970_ = crate::leanh::lean_ctor_get(v_a_2955_, 9);
                    v_quotContext_2971_ = crate::leanh::lean_ctor_get(v_a_2955_, 10);
                    v_currMacroScope_2972_ = crate::leanh::lean_ctor_get(v_a_2955_, 11);
                    v_diag_2973_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_2955_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_2974_ = crate::leanh::lean_ctor_get(v_a_2955_, 12);
                    v_suppressElabErrors_2975_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_2955_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_2976_ = crate::leanh::lean_ctor_get(v_a_2955_, 13);
                    v___x_2977_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2978_ = l_Lean_Syntax_getArg(v_stx_2949_, v___x_2977_);
                    v___x_2979_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4_once
                        ),
                        _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4,
                    );
                    v___x_2980_ = 0;
                    v___x_2981_ = crate::leanh::lean_box(0);
                    v_ref_2982_ = l_Lean_replaceRef(v___x_2978_, v_ref_2966_);
                    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2976_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_2974_);
                    crate::leanh::lean_inc(v_currMacroScope_2972_);
                    crate::leanh::lean_inc(v_quotContext_2971_);
                    crate::leanh::lean_inc(v_maxHeartbeats_2970_);
                    crate::leanh::lean_inc(v_initHeartbeats_2969_);
                    crate::leanh::lean_inc(v_openDecls_2968_);
                    crate::leanh::lean_inc(v_currNamespace_2967_);
                    crate::leanh::lean_inc(v_ref_2982_);
                    crate::leanh::lean_inc(v_maxRecDepth_2965_);
                    crate::leanh::lean_inc(v_currRecDepth_2964_);
                    crate::leanh::lean_inc_ref(v_options_2963_);
                    crate::leanh::lean_inc_ref(v_fileMap_2962_);
                    crate::leanh::lean_inc_ref(v_fileName_2961_);
                    v___x_2983_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_2983_, 0, v_fileName_2961_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 1, v_fileMap_2962_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 2, v_options_2963_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 3, v_currRecDepth_2964_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 4, v_maxRecDepth_2965_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 5, v_ref_2982_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 6, v_currNamespace_2967_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 7, v_openDecls_2968_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 8, v_initHeartbeats_2969_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 9, v_maxHeartbeats_2970_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 10, v_quotContext_2971_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 11, v_currMacroScope_2972_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 12, v_cancelTk_x3f_2974_);
                    crate::leanh::lean_ctor_set(v___x_2983_, 13, v_inheritedTraceOptions_2976_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2983_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                        v_diag_2973_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2983_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_2975_,
                    );
                    v___x_2984_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_2979_,
                        v___x_2980_,
                        v___x_2981_,
                        v_a_2953_,
                        v_a_2954_,
                        v___x_2983_,
                        v_a_2956_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2984_) == 0 {
                        v_a_2985_ = crate::leanh::lean_ctor_get(v___x_2984_, 0);
                        v_isSharedCheck_3125_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2984_)) as u8;
                        if v_isSharedCheck_3125_ == 0 {
                            v___x_2987_ = v___x_2984_;
                            v_isShared_2988_ = v_isSharedCheck_3125_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2985_);
                            crate::leanh::lean_dec(v___x_2984_);
                            v___x_2987_ = crate::leanh::lean_box(0);
                            v_isShared_2988_ = v_isSharedCheck_3125_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2983_, 14);
                        crate::leanh::lean_dec(v_ref_2982_);
                        crate::leanh::lean_dec(v___x_2978_);
                        crate::leanh::lean_dec(v_expectedType_x3f_2950_);
                        crate::leanh::lean_dec(v_stx_2949_);
                        return v___x_2984_;
                    }
                }
            }
            1 => {
                v___x_2989_ = crate::leanh::lean_unsigned_to_nat(0);
                v_tk_2990_ = l_Lean_Syntax_getArg(v_stx_2949_, v___x_2989_);
                crate::leanh::lean_dec(v_stx_2949_);
                v___x_3069_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2_once
                    ),
                    _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2,
                );
                if crate::leanh::lean_obj_tag(v_expectedType_x3f_2950_) == 0 {
                    v___y_3071_ = v_a_2985_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_2985_);
                    v_val_3124_ = crate::leanh::lean_ctor_get(v_expectedType_x3f_2950_, 0);
                    crate::leanh::lean_inc(v_val_3124_);
                    crate::leanh::lean_dec_ref_known(v_expectedType_x3f_2950_, 1);
                    v___y_3071_ = v_val_3124_;
                    state = 15;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_2992_) == 0 {
                    crate::leanh::lean_del_object(v___x_2987_);
                    v_a_2999_ = crate::leanh::lean_ctor_get(v___y_2992_, 0);
                    v_isSharedCheck_3009_ = (!crate::leanh::lean_is_exclusive(v___y_2992_)) as u8;
                    if v_isSharedCheck_3009_ == 0 {
                        v___x_3001_ = v___y_2992_;
                        v_isShared_3002_ = v_isSharedCheck_3009_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2999_);
                        crate::leanh::lean_dec(v___y_2992_);
                        v___x_3001_ = crate::leanh::lean_box(0);
                        v_isShared_3002_ = v_isSharedCheck_3009_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2997_);
                    crate::leanh::lean_dec(v_tk_2990_);
                    v_a_3010_ = crate::leanh::lean_ctor_get(v___y_2992_, 0);
                    crate::leanh::lean_inc(v_a_3010_);
                    crate::leanh::lean_dec_ref_known(v___y_2992_, 1);
                    if v_isShared_2988_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2987_, 0, v_a_3010_);
                        v___x_3012_ = v___x_2987_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3013_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3010_);
                        v___x_3012_ = v_reuseFailAlloc_3013_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3003_ = lean_io_error_to_string(v_a_2999_);
                if v_isShared_3002_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3001_, 3);
                    crate::leanh::lean_ctor_set(v___x_3001_, 0, v___x_3003_);
                    v___x_3005_ = v___x_3001_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3008_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3003_);
                    v___x_3005_ = v_reuseFailAlloc_3008_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3006_ = l_Lean_MessageData_ofFormat(v___x_3005_);
                v___x_3007_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(v_tk_2990_, v___x_3006_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
                crate::leanh::lean_dec_ref(v___y_2997_);
                crate::leanh::lean_dec(v_tk_2990_);
                return v___x_3007_;
            }
            5 => {
                return v___x_3012_;
            }
            6 => {
                v___x_3022_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6;
                v___x_3023_ = lean_mk_empty_array_with_capacity(v___x_2977_);
                v___x_3024_ = lean_array_push(v___x_3023_, v___y_3015_);
                v___x_3025_ = l_Lean_Meta_mkAppM(
                    v___x_3022_,
                    v___x_3024_,
                    v___y_3018_,
                    v___y_3019_,
                    v___y_3020_,
                    v___y_3021_,
                );
                if crate::leanh::lean_obj_tag(v___x_3025_) == 0 {
                    v_a_3026_ = crate::leanh::lean_ctor_get(v___x_3025_, 0);
                    v_isSharedCheck_3068_ = (!crate::leanh::lean_is_exclusive(v___x_3025_)) as u8;
                    if v_isSharedCheck_3068_ == 0 {
                        v___x_3028_ = v___x_3025_;
                        v_isShared_3029_ = v_isSharedCheck_3068_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3026_);
                        crate::leanh::lean_dec(v___x_3025_);
                        v___x_3028_ = crate::leanh::lean_box(0);
                        v_isShared_3029_ = v_isSharedCheck_3068_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3020_);
                    crate::leanh::lean_dec(v_tk_2990_);
                    crate::leanh::lean_del_object(v___x_2987_);
                    return v___x_3025_;
                }
            }
            7 => {
                v___x_3030_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1(
                    v_a_3026_,
                    v___y_3018_,
                    v___y_3019_,
                    v___y_3020_,
                    v___y_3021_,
                );
                if crate::leanh::lean_obj_tag(v___x_3030_) == 0 {
                    v_a_3031_ = crate::leanh::lean_ctor_get(v___x_3030_, 0);
                    crate::leanh::lean_inc(v_a_3031_);
                    crate::leanh::lean_dec_ref_known(v___x_3030_, 1);
                    v___f_3032_ = crate::leanh::lean_alloc_closure(
                        l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0___boxed
                            as *mut core::ffi::c_void,
                        8,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3032_, 0, v_a_3031_);
                    v___x_3033_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(v___f_3032_, v___x_2959_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
                    if crate::leanh::lean_obj_tag(v___x_3033_) == 0 {
                        v_a_3034_ = crate::leanh::lean_ctor_get(v___x_3033_, 0);
                        crate::leanh::lean_inc(v_a_3034_);
                        crate::leanh::lean_dec_ref_known(v___x_3033_, 1);
                        v_fst_3035_ = crate::leanh::lean_ctor_get(v_a_3034_, 0);
                        crate::leanh::lean_inc(v_fst_3035_);
                        v_snd_3036_ = crate::leanh::lean_ctor_get(v_a_3034_, 1);
                        crate::leanh::lean_inc(v_snd_3036_);
                        crate::leanh::lean_dec(v_a_3034_);
                        v___x_3037_ = lean_string_utf8_byte_size(v_fst_3035_);
                        v___x_3038_ = lean_nat_dec_eq(v___x_3037_, v___x_2989_);
                        if v___x_3038_ == 0 {
                            if v_isShared_3029_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_3028_, 3);
                                crate::leanh::lean_ctor_set(v___x_3028_, 0, v_fst_3035_);
                                v___x_3040_ = v___x_3028_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_3051_ =
                                    crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_fst_3035_);
                                v___x_3040_ = v_reuseFailAlloc_3051_;
                                state = 8;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_3035_);
                            crate::leanh::lean_del_object(v___x_3028_);
                            v___y_2992_ = v_snd_3036_;
                            v___y_2993_ = v___y_3016_;
                            v___y_2994_ = v___y_3017_;
                            v___y_2995_ = v___y_3018_;
                            v___y_2996_ = v___y_3019_;
                            v___y_2997_ = v___y_3020_;
                            v___y_2998_ = v___y_3021_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3028_);
                        crate::leanh::lean_dec_ref(v___y_3020_);
                        crate::leanh::lean_dec(v_tk_2990_);
                        crate::leanh::lean_del_object(v___x_2987_);
                        v_a_3052_ = crate::leanh::lean_ctor_get(v___x_3033_, 0);
                        v_isSharedCheck_3059_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3033_)) as u8;
                        if v_isSharedCheck_3059_ == 0 {
                            v___x_3054_ = v___x_3033_;
                            v_isShared_3055_ = v_isSharedCheck_3059_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3052_);
                            crate::leanh::lean_dec(v___x_3033_);
                            v___x_3054_ = crate::leanh::lean_box(0);
                            v_isShared_3055_ = v_isSharedCheck_3059_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3028_);
                    crate::leanh::lean_dec_ref(v___y_3020_);
                    crate::leanh::lean_dec(v_tk_2990_);
                    crate::leanh::lean_del_object(v___x_2987_);
                    v_a_3060_ = crate::leanh::lean_ctor_get(v___x_3030_, 0);
                    v_isSharedCheck_3067_ = (!crate::leanh::lean_is_exclusive(v___x_3030_)) as u8;
                    if v_isSharedCheck_3067_ == 0 {
                        v___x_3062_ = v___x_3030_;
                        v_isShared_3063_ = v_isSharedCheck_3067_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3060_);
                        crate::leanh::lean_dec(v___x_3030_);
                        v___x_3062_ = crate::leanh::lean_box(0);
                        v_isShared_3063_ = v_isSharedCheck_3067_;
                        state = 13;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3041_ = l_Lean_MessageData_ofFormat(v___x_3040_);
                v___x_3042_ =
                    l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4(
                        v_tk_2990_,
                        v___x_3041_,
                        v___y_3016_,
                        v___y_3017_,
                        v___y_3018_,
                        v___y_3019_,
                        v___y_3020_,
                        v___y_3021_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3042_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3042_, 1);
                    v___y_2992_ = v_snd_3036_;
                    v___y_2993_ = v___y_3016_;
                    v___y_2994_ = v___y_3017_;
                    v___y_2995_ = v___y_3018_;
                    v___y_2996_ = v___y_3019_;
                    v___y_2997_ = v___y_3020_;
                    v___y_2998_ = v___y_3021_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_3036_);
                    crate::leanh::lean_dec_ref(v___y_3020_);
                    crate::leanh::lean_dec(v_tk_2990_);
                    crate::leanh::lean_del_object(v___x_2987_);
                    v_a_3043_ = crate::leanh::lean_ctor_get(v___x_3042_, 0);
                    v_isSharedCheck_3050_ = (!crate::leanh::lean_is_exclusive(v___x_3042_)) as u8;
                    if v_isSharedCheck_3050_ == 0 {
                        v___x_3045_ = v___x_3042_;
                        v_isShared_3046_ = v_isSharedCheck_3050_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3043_);
                        crate::leanh::lean_dec(v___x_3042_);
                        v___x_3045_ = crate::leanh::lean_box(0);
                        v_isShared_3046_ = v_isSharedCheck_3050_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3046_ == 0 {
                    v___x_3048_ = v___x_3045_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
                    v___x_3048_ = v_reuseFailAlloc_3049_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3048_;
            }
            11 => {
                if v_isShared_3055_ == 0 {
                    v___x_3057_ = v___x_3054_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3058_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
                    v___x_3057_ = v_reuseFailAlloc_3058_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3057_;
            }
            13 => {
                if v_isShared_3063_ == 0 {
                    v___x_3065_ = v___x_3062_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
                    v___x_3065_ = v_reuseFailAlloc_3066_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3065_;
            }
            15 => {
                v___x_3072_ = l_Lean_Expr_app___override(v___x_3069_, v___y_3071_);
                v___x_3073_ = 0;
                v___x_3074_ = l_Lean_SourceInfo_fromRef(v_ref_2982_, v___x_3073_);
                crate::leanh::lean_dec(v_ref_2982_);
                v___x_3075_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9;
                v___x_3076_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10;
                crate::leanh::lean_inc(v___x_3074_);
                v___x_3077_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3077_, 0, v___x_3074_);
                crate::leanh::lean_ctor_set(v___x_3077_, 1, v___x_3075_);
                v___x_3078_ =
                    l_Lean_Syntax_node2(v___x_3074_, v___x_3076_, v___x_3077_, v___x_2978_);
                v___x_3079_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3079_, 0, v___x_3072_);
                v___x_3080_ = crate::leanh::lean_box(0);
                v___x_3081_ = l_Lean_Elab_Term_elabTermEnsuringType(
                    v___x_3078_,
                    v___x_3079_,
                    v___x_2959_,
                    v___x_2959_,
                    v___x_3080_,
                    v_a_2951_,
                    v_a_2952_,
                    v_a_2953_,
                    v_a_2954_,
                    v___x_2983_,
                    v_a_2956_,
                );
                if crate::leanh::lean_obj_tag(v___x_3081_) == 0 {
                    v_a_3082_ = crate::leanh::lean_ctor_get(v___x_3081_, 0);
                    crate::leanh::lean_inc(v_a_3082_);
                    crate::leanh::lean_dec_ref_known(v___x_3081_, 1);
                    v___x_3083_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(
                        v___x_3073_,
                        v_a_2951_,
                        v_a_2952_,
                        v_a_2953_,
                        v_a_2954_,
                        v___x_2983_,
                        v_a_2956_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3083_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3083_, 1);
                        v___x_3084_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(v_a_3082_, v_a_2954_);
                        v_a_3085_ = crate::leanh::lean_ctor_get(v___x_3084_, 0);
                        crate::leanh::lean_inc_n(v_a_3085_, 2);
                        crate::leanh::lean_dec_ref(v___x_3084_);
                        v___x_3086_ = l_Lean_Meta_getMVars(
                            v_a_3085_,
                            v_a_2953_,
                            v_a_2954_,
                            v___x_2983_,
                            v_a_2956_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3086_) == 0 {
                            v_a_3087_ = crate::leanh::lean_ctor_get(v___x_3086_, 0);
                            crate::leanh::lean_inc(v_a_3087_);
                            crate::leanh::lean_dec_ref_known(v___x_3086_, 1);
                            v___x_3088_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                                v_a_3087_,
                                v___x_3080_,
                                v_a_2951_,
                                v_a_2952_,
                                v_a_2953_,
                                v_a_2954_,
                                v___x_2983_,
                                v_a_2956_,
                            );
                            crate::leanh::lean_dec(v_a_3087_);
                            if crate::leanh::lean_obj_tag(v___x_3088_) == 0 {
                                v_a_3089_ = crate::leanh::lean_ctor_get(v___x_3088_, 0);
                                crate::leanh::lean_inc(v_a_3089_);
                                crate::leanh::lean_dec_ref_known(v___x_3088_, 1);
                                v___x_3090_ = (crate::leanh::lean_unbox(v_a_3089_) as u8);
                                crate::leanh::lean_dec(v_a_3089_);
                                if v___x_3090_ == 0 {
                                    v___y_3015_ = v_a_3085_;
                                    v___y_3016_ = v_a_2951_;
                                    v___y_3017_ = v_a_2952_;
                                    v___y_3018_ = v_a_2953_;
                                    v___y_3019_ = v_a_2954_;
                                    v___y_3020_ = v___x_2983_;
                                    v___y_3021_ = v_a_2956_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_3085_);
                                    crate::leanh::lean_dec(v_tk_2990_);
                                    crate::leanh::lean_del_object(v___x_2987_);
                                    crate::leanh::lean_dec_ref_known(v___x_2983_, 14);
                                    v___x_3091_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg();
                                    v_a_3092_ = crate::leanh::lean_ctor_get(v___x_3091_, 0);
                                    v_isSharedCheck_3099_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3091_)) as u8;
                                    if v_isSharedCheck_3099_ == 0 {
                                        v___x_3094_ = v___x_3091_;
                                        v_isShared_3095_ = v_isSharedCheck_3099_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3092_);
                                        crate::leanh::lean_dec(v___x_3091_);
                                        v___x_3094_ = crate::leanh::lean_box(0);
                                        v_isShared_3095_ = v_isSharedCheck_3099_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3085_);
                                crate::leanh::lean_dec(v_tk_2990_);
                                crate::leanh::lean_del_object(v___x_2987_);
                                crate::leanh::lean_dec_ref_known(v___x_2983_, 14);
                                v_a_3100_ = crate::leanh::lean_ctor_get(v___x_3088_, 0);
                                v_isSharedCheck_3107_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3088_)) as u8;
                                if v_isSharedCheck_3107_ == 0 {
                                    v___x_3102_ = v___x_3088_;
                                    v_isShared_3103_ = v_isSharedCheck_3107_;
                                    state = 18;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3100_);
                                    crate::leanh::lean_dec(v___x_3088_);
                                    v___x_3102_ = crate::leanh::lean_box(0);
                                    v_isShared_3103_ = v_isSharedCheck_3107_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3085_);
                            crate::leanh::lean_dec(v_tk_2990_);
                            crate::leanh::lean_del_object(v___x_2987_);
                            crate::leanh::lean_dec_ref_known(v___x_2983_, 14);
                            v_a_3108_ = crate::leanh::lean_ctor_get(v___x_3086_, 0);
                            v_isSharedCheck_3115_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3086_)) as u8;
                            if v_isSharedCheck_3115_ == 0 {
                                v___x_3110_ = v___x_3086_;
                                v_isShared_3111_ = v_isSharedCheck_3115_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3108_);
                                crate::leanh::lean_dec(v___x_3086_);
                                v___x_3110_ = crate::leanh::lean_box(0);
                                v_isShared_3111_ = v_isSharedCheck_3115_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3082_);
                        crate::leanh::lean_dec(v_tk_2990_);
                        crate::leanh::lean_del_object(v___x_2987_);
                        crate::leanh::lean_dec_ref_known(v___x_2983_, 14);
                        v_a_3116_ = crate::leanh::lean_ctor_get(v___x_3083_, 0);
                        v_isSharedCheck_3123_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3083_)) as u8;
                        if v_isSharedCheck_3123_ == 0 {
                            v___x_3118_ = v___x_3083_;
                            v_isShared_3119_ = v_isSharedCheck_3123_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3116_);
                            crate::leanh::lean_dec(v___x_3083_);
                            v___x_3118_ = crate::leanh::lean_box(0);
                            v_isShared_3119_ = v_isSharedCheck_3123_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_tk_2990_);
                    crate::leanh::lean_del_object(v___x_2987_);
                    crate::leanh::lean_dec_ref_known(v___x_2983_, 14);
                    return v___x_3081_;
                }
            }
            16 => {
                if v_isShared_3095_ == 0 {
                    v___x_3097_ = v___x_3094_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
                    v___x_3097_ = v_reuseFailAlloc_3098_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3097_;
            }
            18 => {
                if v_isShared_3103_ == 0 {
                    v___x_3105_ = v___x_3102_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
                    v___x_3105_ = v_reuseFailAlloc_3106_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3105_;
            }
            20 => {
                if v_isShared_3111_ == 0 {
                    v___x_3113_ = v___x_3110_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3114_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
                    v___x_3113_ = v_reuseFailAlloc_3114_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3113_;
            }
            22 => {
                if v_isShared_3119_ == 0 {
                    v___x_3121_ = v___x_3118_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3122_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
                    v___x_3121_ = v_reuseFailAlloc_3122_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___boxed(
    mut v_stx_3126_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_3127_: *mut crate::leanh::LeanObject,
    mut v_a_3128_: *mut crate::leanh::LeanObject,
    mut v_a_3129_: *mut crate::leanh::LeanObject,
    mut v_a_3130_: *mut crate::leanh::LeanObject,
    mut v_a_3131_: *mut crate::leanh::LeanObject,
    mut v_a_3132_: *mut crate::leanh::LeanObject,
    mut v_a_3133_: *mut crate::leanh::LeanObject,
    mut v_a_3134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3135_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO(
        v_stx_3126_,
        v_expectedType_x3f_3127_,
        v_a_3128_,
        v_a_3129_,
        v_a_3130_,
        v_a_3131_,
        v_a_3132_,
        v_a_3133_,
    );
    crate::leanh::lean_dec(v_a_3133_);
    crate::leanh::lean_dec_ref(v_a_3132_);
    crate::leanh::lean_dec(v_a_3131_);
    crate::leanh::lean_dec_ref(v_a_3130_);
    crate::leanh::lean_dec(v_a_3129_);
    crate::leanh::lean_dec_ref(v_a_3128_);
    return v_res_3135_;
}
pub unsafe fn l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3(
    mut v_00_u03b1_3136_: *mut crate::leanh::LeanObject,
    mut v_h_3137_: *mut crate::leanh::LeanObject,
    mut v_x_3138_: *mut crate::leanh::LeanObject,
    mut v___y_3139_: *mut crate::leanh::LeanObject,
    mut v___y_3140_: *mut crate::leanh::LeanObject,
    mut v___y_3141_: *mut crate::leanh::LeanObject,
    mut v___y_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
    mut v___y_3144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3146_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(v_h_3137_, v_x_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
    return v___x_3146_;
}
pub unsafe fn l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___boxed(
    mut v_00_u03b1_3147_: *mut crate::leanh::LeanObject,
    mut v_h_3148_: *mut crate::leanh::LeanObject,
    mut v_x_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
    mut v___y_3153_: *mut crate::leanh::LeanObject,
    mut v___y_3154_: *mut crate::leanh::LeanObject,
    mut v___y_3155_: *mut crate::leanh::LeanObject,
    mut v___y_3156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3157_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3(v_00_u03b1_3147_, v_h_3148_, v_x_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
    crate::leanh::lean_dec(v___y_3155_);
    crate::leanh::lean_dec_ref(v___y_3154_);
    crate::leanh::lean_dec(v___y_3153_);
    crate::leanh::lean_dec_ref(v___y_3152_);
    crate::leanh::lean_dec(v___y_3151_);
    crate::leanh::lean_dec_ref(v___y_3150_);
    return v_res_3157_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2(
    mut v_00_u03b1_3158_: *mut crate::leanh::LeanObject,
    mut v_x_3159_: *mut crate::leanh::LeanObject,
    mut v_isolateStderr_3160_: u8,
    mut v___y_3161_: *mut crate::leanh::LeanObject,
    mut v___y_3162_: *mut crate::leanh::LeanObject,
    mut v___y_3163_: *mut crate::leanh::LeanObject,
    mut v___y_3164_: *mut crate::leanh::LeanObject,
    mut v___y_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(v_x_3159_, v_isolateStderr_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
    return v___x_3168_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___boxed(
    mut v_00_u03b1_3169_: *mut crate::leanh::LeanObject,
    mut v_x_3170_: *mut crate::leanh::LeanObject,
    mut v_isolateStderr_3171_: *mut crate::leanh::LeanObject,
    mut v___y_3172_: *mut crate::leanh::LeanObject,
    mut v___y_3173_: *mut crate::leanh::LeanObject,
    mut v___y_3174_: *mut crate::leanh::LeanObject,
    mut v___y_3175_: *mut crate::leanh::LeanObject,
    mut v___y_3176_: *mut crate::leanh::LeanObject,
    mut v___y_3177_: *mut crate::leanh::LeanObject,
    mut v___y_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isolateStderr_boxed_3179_: u8 = 0;
    let mut v_res_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isolateStderr_boxed_3179_ = (crate::leanh::lean_unbox(v_isolateStderr_3171_) as u8);
    v_res_3180_ =
        l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2(
            v_00_u03b1_3169_,
            v_x_3170_,
            v_isolateStderr_boxed_3179_,
            v___y_3172_,
            v___y_3173_,
            v___y_3174_,
            v___y_3175_,
            v___y_3176_,
            v___y_3177_,
        );
    crate::leanh::lean_dec(v___y_3177_);
    crate::leanh::lean_dec_ref(v___y_3176_);
    crate::leanh::lean_dec(v___y_3175_);
    crate::leanh::lean_dec_ref(v___y_3174_);
    crate::leanh::lean_dec(v___y_3173_);
    crate::leanh::lean_dec_ref(v___y_3172_);
    return v_res_3180_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3(
    mut v_00_u03b1_3181_: *mut crate::leanh::LeanObject,
    mut v_ref_3182_: *mut crate::leanh::LeanObject,
    mut v_msg_3183_: *mut crate::leanh::LeanObject,
    mut v___y_3184_: *mut crate::leanh::LeanObject,
    mut v___y_3185_: *mut crate::leanh::LeanObject,
    mut v___y_3186_: *mut crate::leanh::LeanObject,
    mut v___y_3187_: *mut crate::leanh::LeanObject,
    mut v___y_3188_: *mut crate::leanh::LeanObject,
    mut v___y_3189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3191_ =
        l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(
            v_ref_3182_,
            v_msg_3183_,
            v___y_3184_,
            v___y_3185_,
            v___y_3186_,
            v___y_3187_,
            v___y_3188_,
            v___y_3189_,
        );
    return v___x_3191_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___boxed(
    mut v_00_u03b1_3192_: *mut crate::leanh::LeanObject,
    mut v_ref_3193_: *mut crate::leanh::LeanObject,
    mut v_msg_3194_: *mut crate::leanh::LeanObject,
    mut v___y_3195_: *mut crate::leanh::LeanObject,
    mut v___y_3196_: *mut crate::leanh::LeanObject,
    mut v___y_3197_: *mut crate::leanh::LeanObject,
    mut v___y_3198_: *mut crate::leanh::LeanObject,
    mut v___y_3199_: *mut crate::leanh::LeanObject,
    mut v___y_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3202_ =
        l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3(
            v_00_u03b1_3192_,
            v_ref_3193_,
            v_msg_3194_,
            v___y_3195_,
            v___y_3196_,
            v___y_3197_,
            v___y_3198_,
            v___y_3199_,
            v___y_3200_,
        );
    crate::leanh::lean_dec(v___y_3200_);
    crate::leanh::lean_dec_ref(v___y_3199_);
    crate::leanh::lean_dec(v___y_3198_);
    crate::leanh::lean_dec_ref(v___y_3197_);
    crate::leanh::lean_dec(v___y_3196_);
    crate::leanh::lean_dec_ref(v___y_3195_);
    crate::leanh::lean_dec(v_ref_3193_);
    return v_res_3202_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7(
    mut v_00_u03b1_3203_: *mut crate::leanh::LeanObject,
    mut v_msg_3204_: *mut crate::leanh::LeanObject,
    mut v___y_3205_: *mut crate::leanh::LeanObject,
    mut v___y_3206_: *mut crate::leanh::LeanObject,
    mut v___y_3207_: *mut crate::leanh::LeanObject,
    mut v___y_3208_: *mut crate::leanh::LeanObject,
    mut v___y_3209_: *mut crate::leanh::LeanObject,
    mut v___y_3210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3212_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(v_msg_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
    return v___x_3212_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___boxed(
    mut v_00_u03b1_3213_: *mut crate::leanh::LeanObject,
    mut v_msg_3214_: *mut crate::leanh::LeanObject,
    mut v___y_3215_: *mut crate::leanh::LeanObject,
    mut v___y_3216_: *mut crate::leanh::LeanObject,
    mut v___y_3217_: *mut crate::leanh::LeanObject,
    mut v___y_3218_: *mut crate::leanh::LeanObject,
    mut v___y_3219_: *mut crate::leanh::LeanObject,
    mut v___y_3220_: *mut crate::leanh::LeanObject,
    mut v___y_3221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3222_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7(v_00_u03b1_3213_, v_msg_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
    crate::leanh::lean_dec(v___y_3220_);
    crate::leanh::lean_dec_ref(v___y_3219_);
    crate::leanh::lean_dec(v___y_3218_);
    crate::leanh::lean_dec_ref(v___y_3217_);
    crate::leanh::lean_dec(v___y_3216_);
    crate::leanh::lean_dec_ref(v___y_3215_);
    return v_res_3222_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9(
    mut v_ref_3223_: *mut crate::leanh::LeanObject,
    mut v_msgData_3224_: *mut crate::leanh::LeanObject,
    mut v_severity_3225_: u8,
    mut v_isSilent_3226_: u8,
    mut v___y_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3234_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(v_ref_3223_, v_msgData_3224_, v_severity_3225_, v_isSilent_3226_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
    return v___x_3234_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___boxed(
    mut v_ref_3235_: *mut crate::leanh::LeanObject,
    mut v_msgData_3236_: *mut crate::leanh::LeanObject,
    mut v_severity_3237_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
    mut v___y_3245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3246_: u8 = 0;
    let mut v_isSilent_boxed_3247_: u8 = 0;
    let mut v_res_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3246_ = (crate::leanh::lean_unbox(v_severity_3237_) as u8);
    v_isSilent_boxed_3247_ = (crate::leanh::lean_unbox(v_isSilent_3238_) as u8);
    v_res_3248_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9(v_ref_3235_, v_msgData_3236_, v_severity_boxed_3246_, v_isSilent_boxed_3247_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
    crate::leanh::lean_dec(v___y_3244_);
    crate::leanh::lean_dec_ref(v___y_3243_);
    crate::leanh::lean_dec(v___y_3242_);
    crate::leanh::lean_dec_ref(v___y_3241_);
    crate::leanh::lean_dec(v___y_3240_);
    crate::leanh::lean_dec_ref(v___y_3239_);
    crate::leanh::lean_dec(v_ref_3235_);
    return v_res_3248_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10(
    mut v_msgData_3249_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
    mut v___y_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
    mut v___y_3255_: *mut crate::leanh::LeanObject,
    mut v___y_3256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3258_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(v_msgData_3249_, v_macroStack_3250_, v___y_3255_);
    return v___x_3258_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___boxed(
    mut v_msgData_3259_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3260_: *mut crate::leanh::LeanObject,
    mut v___y_3261_: *mut crate::leanh::LeanObject,
    mut v___y_3262_: *mut crate::leanh::LeanObject,
    mut v___y_3263_: *mut crate::leanh::LeanObject,
    mut v___y_3264_: *mut crate::leanh::LeanObject,
    mut v___y_3265_: *mut crate::leanh::LeanObject,
    mut v___y_3266_: *mut crate::leanh::LeanObject,
    mut v___y_3267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3268_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10(v_msgData_3259_, v_macroStack_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
    crate::leanh::lean_dec(v___y_3266_);
    crate::leanh::lean_dec_ref(v___y_3265_);
    crate::leanh::lean_dec(v___y_3264_);
    crate::leanh::lean_dec_ref(v___y_3263_);
    crate::leanh::lean_dec(v___y_3262_);
    crate::leanh::lean_dec_ref(v___y_3261_);
    return v_res_3268_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3274_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_3275_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1;
    v___x_3276_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__1;
    v___x_3277_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_3278_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3274_,
        v___x_3275_,
        v___x_3276_,
        v___x_3277_,
    );
    return v___x_3278_;
}
pub unsafe fn l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___boxed(
    mut v_a_3279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3280_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1();
    return v_res_3280_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Meta(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ToExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Eval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Meta(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Meta(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ToExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Eval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_DSL_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_Meta(builtin);
}
