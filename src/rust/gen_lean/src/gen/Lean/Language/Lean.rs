// Lean compiler output
// Module: Lean.Language.Lean
// Imports: Lean.Language.Util Lean.Language.Lean.Types Lean.Elab.Import
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_float_div, lean_get_set_stderr, lean_get_set_stdin,
    lean_get_set_stdout, lean_io_as_task, lean_io_bind_task, lean_io_mono_nanos_now,
    lean_io_promise_new, lean_io_promise_resolve, lean_mk_empty_array_with_capacity, lean_mk_thunk,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_panic_fn_borrowed, lean_profileit, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_append, lean_string_dec_eq, lean_string_from_utf8_unchecked,
    lean_string_utf8_byte_size, lean_string_validate_utf8, lean_task_map, lean_task_pure,
    lean_thunk_get_own, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::String::Basic::l_String_firstDiffPos;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toNat_x3f;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Name_getRoot, l_Lean_Name_replacePrefix, l_Lean_Syntax_unsetTrailing,
};
use crate::r#gen::Init::Prelude::{
    l_ByteArray_empty, l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_firstFrontendMacroScope,
    l_Lean_replaceRef,
};
use crate::r#gen::Init::System::CancelToken::{l_IO_CancelToken_isSet, l_IO_CancelToken_new};
use crate::r#gen::Init::System::IO::{l_BaseIO_chainTask___redArg, l_IO_FS_Stream_ofBuffer};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::System::Promise::l_IO_Promise_result_x21___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_getMaxHeartbeats, l_Lean_Core_stderrAsMessages, l_Lean_DeclNameGenerator_ofPrefix,
    l_Lean_diagnostics, l_Lean_internal_cmdlineSnapshots,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::{
    l_Lean_Options_empty, l_Lean_getOptionDecls, lean_register_option,
};
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Array_toPArray_x27___redArg, l_Lean_PersistentArray_get_x21___redArg,
    l_List_toPArray_x27___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_elabCommandTopLevel, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_getScope___redArg, l_Lean_Elab_Command_mkState,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_isAbortExceptionId;
use crate::r#gen::Lean::Elab::Import::{
    initialize_Lean_Elab_Import, l_Lean_Elab_HeaderSyntax_startPos, l_Lean_Elab_processHeaderCore,
    runtime_initialize_Lean_Elab_Import,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_InfoState_substituteLazy, l_Lean_Elab_InfoTree_format,
};
use crate::r#gen::Lean::Elab::InfoTree::Types::l_Lean_Elab_instInhabitedInfoTree_default;
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::InternalExceptionId::l_Lean_InternalExceptionId_getName;
use crate::r#gen::Lean::Language::Basic::{
    l_Lean_Language_Snapshot_Diagnostics_empty, l_Lean_Language_Snapshot_Diagnostics_ofMessageLog,
    l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting,
    l_Lean_Language_SnapshotTask_bindIO___redArg, l_Lean_Language_SnapshotTask_cancelRec___redArg,
    l_Lean_Language_SnapshotTask_defaultReportingRange,
    l_Lean_Language_SnapshotTask_finished___redArg, l_Lean_Language_SnapshotTask_get___redArg,
    l_Lean_Language_SnapshotTask_get_x3f___redArg, l_Lean_Language_SnapshotTask_ofIO___redArg,
    l_Lean_Language_SnapshotTree_waitAll, l_Lean_Language_diagnosticsOfHeaderError,
    l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_,
    l_Lean_Language_instInhabitedDynamicSnapshot, l_Lean_Language_instInhabitedSnapshotLeaf,
    l_Lean_Language_instInhabitedSnapshotTask_default___redArg,
    l_Lean_Language_instInhabitedSnapshotTree_default,
    l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed,
};
use crate::r#gen::Lean::Language::Lean::Types::{
    initialize_Lean_Language_Lean_Types, l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult,
    l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go,
    l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot,
    runtime_initialize_Lean_Language_Lean_Types,
};
use crate::r#gen::Lean::Language::Util::{
    initialize_Lean_Language_Util, l_Lean_Language_SnapshotTree_trace,
    runtime_initialize_Lean_Language_Util,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_nil,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageLog_add,
    l_Lean_MessageLog_empty, l_Lean_MessageLog_hasErrors, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Parser::Module::{
    l_Lean_Parser_instInhabitedModuleParserState_default, l_Lean_Parser_isTerminalCommand,
    l_Lean_Parser_parseCommand, l_Lean_Parser_parseHeader,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_eqWithInfo;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_inheritedTraceOptions,
    l_Lean_instInhabitedTraceState_default, l_Lean_trace_profiler_output,
    l_Lean_trace_profiler_serve,
};
pub static l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___closed__0_value:
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
    m_fun: l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___closed__0_value:
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
    m_fun: l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___lam__0
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0_value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [76, 97, 110, 103, 117, 97, 103, 101, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4_value) as *mut leanh::LeanObject,12305631503237173935 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value) as *mut leanh::LeanObject,3876652420106973250 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,16907900423347910947 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value) as *mut leanh::LeanObject,12657121022815957614 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4_value) as *mut leanh::LeanObject,18140831121073425683 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value) as *mut leanh::LeanObject,108696696180591230 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__11_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [119, 105, 116, 104, 72, 101, 97, 100, 101, 114, 69, 120, 99, 101, 112, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__11_value) as *mut leanh::LeanObject,17822544666029255264 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0_value:
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
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1_value:
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
            l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0_value
        ) as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_setOption___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Language_Lean_setOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Lean_setOption___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_setOption___closed__1_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
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
static mut l_Lean_Language_Lean_setOption___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Lean_setOption___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_setOption___closed__2_value: leanh::LeanStringObject<53> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 53,
        m_capacity: 53,
        m_length: 52,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 45, 68, 32, 112, 97, 114, 97, 109, 101, 116, 101,
            114, 44, 32, 105, 110, 118, 97, 108, 105, 100, 32, 99, 111, 110, 102, 105, 103, 117,
            114, 97, 116, 105, 111, 110, 32, 111, 112, 116, 105, 111, 110, 32, 39, 0,
        ],
    };
static mut l_Lean_Language_Lean_setOption___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Lean_setOption___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_setOption___closed__3_value: leanh::LeanStringObject<31> =
    leanh::LeanStringObject {
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
            39, 32, 118, 97, 108, 117, 101, 44, 32, 105, 116, 32, 109, 117, 115, 116, 32, 98, 101,
            32, 116, 114, 117, 101, 47, 102, 97, 108, 115, 101, 0,
        ],
    };
static mut l_Lean_Language_Lean_setOption___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Lean_setOption___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_setOption___closed__4_value: leanh::LeanStringObject<37> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            39, 32, 118, 97, 108, 117, 101, 44, 32, 105, 116, 32, 109, 117, 115, 116, 32, 98, 101,
            32, 97, 32, 110, 97, 116, 117, 114, 97, 108, 32, 110, 117, 109, 98, 101, 114, 0,
        ],
    };
static mut l_Lean_Language_Lean_setOption___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Lean_setOption___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_setOption___closed__5_value: leanh::LeanStringObject<45> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 45,
        m_capacity: 45,
        m_length: 44,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 45, 68, 32, 112, 97, 114, 97, 109, 101, 116, 101,
            114, 44, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 32, 111,
            112, 116, 105, 111, 110, 32, 39, 0,
        ],
    };
static mut l_Lean_Language_Lean_setOption___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Lean_setOption___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Language_Lean_setOption___closed__6_value: leanh::LeanStringObject<60> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 60,
        m_capacity: 60,
        m_length: 59,
        m_data: [
            39, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 115, 101, 116, 32, 105, 110, 32,
            116, 104, 101, 32, 99, 111, 109, 109, 97, 110, 100, 32, 108, 105, 110, 101, 44, 32,
            117, 115, 101, 32, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 99, 111, 109,
            109, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Language_Lean_setOption___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Lean_setOption___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [119, 101, 97, 107, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__0_value) as *mut leanh::LeanObject,9977606089345140031 as *mut leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__2_value: leanh::LeanStringObject<53> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 45, 68, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 44, 32, 117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 32, 111, 112, 116, 105, 111, 110, 32, 39, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__3_value: leanh::LeanStringObject<50> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [39, 10, 10, 73, 102, 32, 116, 104, 101, 32, 111, 112, 116, 105, 111, 110, 32, 105, 115, 32, 100, 101, 102, 105, 110, 101, 100, 32, 105, 110, 32, 97, 32, 108, 105, 98, 114, 97, 114, 121, 44, 32, 117, 115, 101, 32, 39, 45, 68, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__4_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [39, 32, 116, 111, 32, 115, 101, 116, 32, 105, 116, 32, 99, 111, 110, 100, 105, 116, 105, 111, 110, 97, 108, 108, 121, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__1_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__1_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__2_value) as *mut leanh::LeanObject,14557702332550915328 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 112, 101, 114, 105, 109, 101, 110, 116, 97, 108, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value) as *mut leanh::LeanObject,2329248898711194313 as *mut leanh::LeanObject] };
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14939669842168771165 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__3_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [110, 111, 45, 111, 112, 44, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__3_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__3_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__3_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4_value) as *mut leanh::LeanObject,6140912203723220827 as *mut leanh::LeanObject] };
static l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value) as *mut leanh::LeanObject,17102826151834148454 as *mut leanh::LeanObject] };
static l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value) as *mut leanh::LeanObject,7741079804130057752 as *mut leanh::LeanObject] };
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10550533812418552024 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Language_Lean_experimental_module: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 58, 32, 0]};
static mut l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 66, 97, 115, 105, 99, 0]};
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 116, 114, 105, 110, 103, 46, 102, 114, 111, 109, 85, 84, 70, 56, 33, 0]};
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0_value:
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
    m_data: [112, 114, 111, 99, 101, 115, 115, 0],
};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0_value) as *mut leanh::LeanObject,1036269841839294217 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__2_value:
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
    m_data: [100, 111, 69, 108, 97, 98, 0],
};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__1_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__2_value
        ) as *mut leanh::LeanObject,
        3944300972148410808 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 117, 110, 105, 113, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value) as *mut leanh::LeanObject,3978731030111751661 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 102, 111, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__0_value) as *mut leanh::LeanObject,12843180897352504333 as *mut leanh::LeanObject] };
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__1_value) as *mut leanh::LeanObject,879967617213164781 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 97, 114, 115, 101, 67, 109, 100, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 110, 97, 112, 115, 104, 111, 116, 84, 114, 101, 101, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__0_value) as *mut leanh::LeanObject,12843180897352504333 as *mut leanh::LeanObject] };
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__0_value) as *mut leanh::LeanObject,11086031300686546955 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 97, 114, 115, 105, 110, 103, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6_value
) as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 109, 112, 111, 114, 116, 0]};
static mut l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__0_value) as *mut leanh::LeanObject,16926796752445426157 as *mut leanh::LeanObject] };
static mut l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 105, 109, 112, 111, 114, 116, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_value) as *mut leanh::LeanObject,18184429917870726625 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [104, 101, 97, 100, 101, 114, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3_value) as *mut leanh::LeanObject,4894643542950963212 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 114, 111, 99, 101, 115, 115, 72, 101, 97, 100, 101, 114, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6: f64 = 0.0;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__7_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [73, 109, 112, 111, 114, 116, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__7_value) as *mut leanh::LeanObject,1911470099238579236 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__9_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 109, 112, 111, 114, 116, 105, 110, 103, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__9_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 97, 114, 115, 101, 72, 101, 97, 100, 101, 114, 0]};
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_value) as *mut leanh::LeanObject,3888285428640870040 as *mut leanh::LeanObject] };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0(
    mut v_00_u03b1_3449_: *mut leanh::LeanObject,
    mut v_act_3450_: *mut leanh::LeanObject,
    mut v_ctx_3451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3453_ = leanh::lean_apply_2(v_act_3450_, v_ctx_3451_, leanh::lean_box(0));
    v___x_3454_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3454_, 0, v___x_3453_);
    return v___x_3454_;
}
pub unsafe fn l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0___boxed(
    mut v_00_u03b1_3455_: *mut leanh::LeanObject,
    mut v_act_3456_: *mut leanh::LeanObject,
    mut v_ctx_3457_: *mut leanh::LeanObject,
    mut v___y_3458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3459_ = l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0(
        v_00_u03b1_3455_,
        v_act_3456_,
        v_ctx_3457_,
    );
    return v_res_3459_;
}
pub unsafe fn l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___lam__0(
    mut v_00_u03b1_3462_: *mut leanh::LeanObject,
    mut v_act_3463_: *mut leanh::LeanObject,
    mut v_ctx_3464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toProcessingContext_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toProcessingContext_3465_ = leanh::lean_ctor_get(v_ctx_3464_, 0);
    leanh::lean_inc_ref(v_toProcessingContext_3465_);
    leanh::lean_dec_ref(v_ctx_3464_);
    v___x_3466_ = leanh::lean_apply_1(v_act_3463_, v_toProcessingContext_3465_);
    return v___x_3466_;
}
pub unsafe fn l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT(
    mut v_m_3468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3469_ = l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___closed__0;
    return v___f_3469_;
}
pub unsafe fn l_Lean_Language_Lean_LeanProcessingM_run___redArg(
    mut v_act_3470_: *mut leanh::LeanObject,
    mut v_oldInputCtx_x3f_3471_: *mut leanh::LeanObject,
    mut v_a_3472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3482_: u8 = 0;
    let mut v_inputString_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputString_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_oldInputCtx_x3f_3471_) == 0 {
                    v___x_3478_ = leanh::lean_box(0);
                    v___y_3475_ = v___x_3478_;
                    state = 1;
                    continue;
                } else {
                    v_val_3479_ = leanh::lean_ctor_get(v_oldInputCtx_x3f_3471_, 0);
                    v_isSharedCheck_3489_ =
                        (!leanh::lean_is_exclusive(v_oldInputCtx_x3f_3471_)) as u8;
                    if v_isSharedCheck_3489_ == 0 {
                        v___x_3481_ = v_oldInputCtx_x3f_3471_;
                        v_isShared_3482_ = v_isSharedCheck_3489_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3479_);
                        leanh::lean_dec(v_oldInputCtx_x3f_3471_);
                        v___x_3481_ = leanh::lean_box(0);
                        v_isShared_3482_ = v_isSharedCheck_3489_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_a_3472_);
                v___x_3476_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3476_, 0, v_a_3472_);
                leanh::lean_ctor_set(v___x_3476_, 1, v___y_3475_);
                v___x_3477_ =
                    leanh::lean_apply_2(v_act_3470_, v___x_3476_, leanh::lean_box(0));
                return v___x_3477_;
            }
            2 => {
                v_inputString_3483_ = leanh::lean_ctor_get(v_val_3479_, 0);
                leanh::lean_inc_ref(v_inputString_3483_);
                leanh::lean_dec(v_val_3479_);
                v_inputString_3484_ = leanh::lean_ctor_get(v_a_3472_, 0);
                v___x_3485_ = l_String_firstDiffPos(v_inputString_3483_, v_inputString_3484_);
                leanh::lean_dec_ref(v_inputString_3483_);
                if v_isShared_3482_ == 0 {
                    leanh::lean_ctor_set(v___x_3481_, 0, v___x_3485_);
                    v___x_3487_ = v___x_3481_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
                    v___x_3487_ = v_reuseFailAlloc_3488_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_3475_ = v___x_3487_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_Lean_LeanProcessingM_run___redArg___boxed(
    mut v_act_3490_: *mut leanh::LeanObject,
    mut v_oldInputCtx_x3f_3491_: *mut leanh::LeanObject,
    mut v_a_3492_: *mut leanh::LeanObject,
    mut v_a_3493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3494_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(
        v_act_3490_,
        v_oldInputCtx_x3f_3491_,
        v_a_3492_,
    );
    leanh::lean_dec_ref(v_a_3492_);
    return v_res_3494_;
}
pub unsafe fn l_Lean_Language_Lean_LeanProcessingM_run(
    mut v_00_u03b1_3495_: *mut leanh::LeanObject,
    mut v_act_3496_: *mut leanh::LeanObject,
    mut v_oldInputCtx_x3f_3497_: *mut leanh::LeanObject,
    mut v_a_3498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3500_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(
        v_act_3496_,
        v_oldInputCtx_x3f_3497_,
        v_a_3498_,
    );
    return v___x_3500_;
}
pub unsafe fn l_Lean_Language_Lean_LeanProcessingM_run___boxed(
    mut v_00_u03b1_3501_: *mut leanh::LeanObject,
    mut v_act_3502_: *mut leanh::LeanObject,
    mut v_oldInputCtx_x3f_3503_: *mut leanh::LeanObject,
    mut v_a_3504_: *mut leanh::LeanObject,
    mut v_a_3505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3506_ = l_Lean_Language_Lean_LeanProcessingM_run(
        v_00_u03b1_3501_,
        v_act_3502_,
        v_oldInputCtx_x3f_3503_,
        v_a_3504_,
    );
    leanh::lean_dec_ref(v_a_3504_);
    return v_res_3506_;
}
pub unsafe fn l_Lean_Language_Lean_isBeforeEditPos(
    mut v_pos_3507_: *mut leanh::LeanObject,
    mut v_a_3508_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_firstDiffPos_x3f_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_firstDiffPos_x3f_3510_ = leanh::lean_ctor_get(v_a_3508_, 1);
    if leanh::lean_obj_tag(v_firstDiffPos_x3f_3510_) == 0 {
        let mut v___x_3511_: u8 = 0;
        v___x_3511_ = 0;
        return v___x_3511_;
    } else {
        let mut v_val_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3513_: u8 = 0;
        v_val_3512_ = leanh::lean_ctor_get(v_firstDiffPos_x3f_3510_, 0);
        v___x_3513_ = lean_nat_dec_lt(v_pos_3507_, v_val_3512_);
        return v___x_3513_;
    }
}
pub unsafe fn l_Lean_Language_Lean_isBeforeEditPos___boxed(
    mut v_pos_3514_: *mut leanh::LeanObject,
    mut v_a_3515_: *mut leanh::LeanObject,
    mut v_a_3516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3517_: u8 = 0;
    let mut v_r_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3517_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3514_, v_a_3515_);
    leanh::lean_dec_ref(v_a_3515_);
    leanh::lean_dec(v_pos_3514_);
    v_r_3518_ = leanh::lean_box((v_res_3517_) as usize);
    return v_r_3518_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3550_: u8 = 0;
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3550_ = 1;
    v___x_3551_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__12;
    v___x_3552_ = l_Lean_Name_toString(v___x_3551_, v___x_3550_);
    return v___x_3552_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3553_ = leanh::lean_unsigned_to_nat(32);
    v___x_3554_ = lean_mk_empty_array_with_capacity(v___x_3553_);
    v___x_3555_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3555_, 0, v___x_3554_);
    return v___x_3555_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3556_: usize = 0;
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3556_ = 5usize;
    v___x_3557_ = leanh::lean_unsigned_to_nat(0);
    v___x_3558_ = leanh::lean_unsigned_to_nat(32);
    v___x_3559_ = lean_mk_empty_array_with_capacity(v___x_3558_);
    v___x_3560_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
    v___x_3561_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3561_, 0, v___x_3560_);
    leanh::lean_ctor_set(v___x_3561_, 1, v___x_3559_);
    leanh::lean_ctor_set(v___x_3561_, 2, v___x_3557_);
    leanh::lean_ctor_set(v___x_3561_, 3, v___x_3557_);
    leanh::lean_ctor_set_usize(v___x_3561_, 4, v___x_3556_);
    return v___x_3561_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: u64 = 0;
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3562_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15);
    v___x_3563_ = 0u64;
    v___x_3564_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_3564_, 0, v___x_3562_);
    leanh::lean_ctor_set_uint64(
        v___x_3564_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3563_,
    );
    return v___x_3564_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(
    mut v_ex_3565_: *mut leanh::LeanObject,
    mut v_act_3566_: *mut leanh::LeanObject,
    mut v_a_3567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_3567_);
    v___x_3569_ = leanh::lean_apply_2(v_act_3566_, v_a_3567_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_3569_) == 0 {
        let mut v_a_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_ex_3565_);
        v_a_3570_ = leanh::lean_ctor_get(v___x_3569_, 0);
        leanh::lean_inc(v_a_3570_);
        leanh::lean_dec_ref_known(v___x_3569_, 1);
        return v_a_3570_;
    } else {
        let mut v_a_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toProcessingContext_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3578_: u8 = 0;
        let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3571_ = leanh::lean_ctor_get(v___x_3569_, 0);
        leanh::lean_inc(v_a_3571_);
        leanh::lean_dec_ref_known(v___x_3569_, 1);
        v_toProcessingContext_3572_ = leanh::lean_ctor_get(v_a_3567_, 0);
        v___x_3573_ = lean_io_error_to_string(v_a_3571_);
        v___x_3574_ =
            l_Lean_Language_diagnosticsOfHeaderError(v___x_3573_, v_toProcessingContext_3572_);
        v___x_3575_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13);
        v___x_3576_ = leanh::lean_box(0);
        v___x_3577_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
        v___x_3578_ = 0;
        v___x_3579_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
        leanh::lean_ctor_set(v___x_3579_, 0, v___x_3575_);
        leanh::lean_ctor_set(v___x_3579_, 1, v___x_3574_);
        leanh::lean_ctor_set(v___x_3579_, 2, v___x_3576_);
        leanh::lean_ctor_set(v___x_3579_, 3, v___x_3577_);
        leanh::lean_ctor_set_uint8(
            v___x_3579_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
            v___x_3578_,
        );
        v___x_3580_ = leanh::lean_apply_1(v_ex_3565_, v___x_3579_);
        return v___x_3580_;
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___boxed(
    mut v_ex_3581_: *mut leanh::LeanObject,
    mut v_act_3582_: *mut leanh::LeanObject,
    mut v_a_3583_: *mut leanh::LeanObject,
    mut v_a_3584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3585_ =
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(
            v_ex_3581_,
            v_act_3582_,
            v_a_3583_,
        );
    leanh::lean_dec_ref(v_a_3583_);
    return v_res_3585_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(
    mut v_00_u03b1_3586_: *mut leanh::LeanObject,
    mut v_ex_3587_: *mut leanh::LeanObject,
    mut v_act_3588_: *mut leanh::LeanObject,
    mut v_a_3589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3591_ =
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(
            v_ex_3587_,
            v_act_3588_,
            v_a_3589_,
        );
    return v___x_3591_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed(
    mut v_00_u03b1_3592_: *mut leanh::LeanObject,
    mut v_ex_3593_: *mut leanh::LeanObject,
    mut v_act_3594_: *mut leanh::LeanObject,
    mut v_a_3595_: *mut leanh::LeanObject,
    mut v_a_3596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3597_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(
        v_00_u03b1_3592_,
        v_ex_3593_,
        v_act_3594_,
        v_a_3595_,
    );
    leanh::lean_dec_ref(v_a_3595_);
    return v_res_3597_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(
    mut v_o_3601_: *mut leanh::LeanObject,
    mut v_k_3602_: *mut leanh::LeanObject,
    mut v_v_3603_: u8,
) -> *mut leanh::LeanObject {
    let mut v_map_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3605_: u8 = 0;
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3608_: u8 = 0;
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: u8 = 0;
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3604_ = leanh::lean_ctor_get(v_o_3601_, 0);
                v_hasTrace_3605_ = leanh::lean_ctor_get_uint8(
                    v_o_3601_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3619_ = (!leanh::lean_is_exclusive(v_o_3601_)) as u8;
                if v_isSharedCheck_3619_ == 0 {
                    v___x_3607_ = v_o_3601_;
                    v_isShared_3608_ = v_isSharedCheck_3619_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_3604_);
                    leanh::lean_dec(v_o_3601_);
                    v___x_3607_ = leanh::lean_box(0);
                    v_isShared_3608_ = v_isSharedCheck_3619_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3609_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_3609_, 0 as u32, v_v_3603_);
                leanh::lean_inc(v_k_3602_);
                v___x_3610_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3602_, v___x_3609_, v_map_3604_);
                if v_hasTrace_3605_ == 0 {
                    v___x_3611_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1;
                    v___x_3612_ = l_Lean_Name_isPrefixOf(v___x_3611_, v_k_3602_);
                    leanh::lean_dec(v_k_3602_);
                    if v_isShared_3608_ == 0 {
                        leanh::lean_ctor_set(v___x_3607_, 0, v___x_3610_);
                        v___x_3614_ = v___x_3607_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3615_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3610_);
                        v___x_3614_ = v_reuseFailAlloc_3615_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_3602_);
                    if v_isShared_3608_ == 0 {
                        leanh::lean_ctor_set(v___x_3607_, 0, v___x_3610_);
                        v___x_3617_ = v___x_3607_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3618_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3610_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_3618_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_3605_,
                        );
                        v___x_3617_ = v_reuseFailAlloc_3618_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3614_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3612_,
                );
                return v___x_3614_;
            }
            3 => {
                return v___x_3617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___boxed(
    mut v_o_3620_: *mut leanh::LeanObject,
    mut v_k_3621_: *mut leanh::LeanObject,
    mut v_v_3622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_3623_: u8 = 0;
    let mut v_res_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_3623_ = (leanh::lean_unbox(v_v_3622_) as u8);
    v_res_3624_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(
        v_o_3620_,
        v_k_3621_,
        v_v_boxed_3623_,
    );
    return v_res_3624_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__1(
    mut v_o_3625_: *mut leanh::LeanObject,
    mut v_k_3626_: *mut leanh::LeanObject,
    mut v_v_3627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3629_: u8 = 0;
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3632_: u8 = 0;
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: u8 = 0;
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3628_ = leanh::lean_ctor_get(v_o_3625_, 0);
                v_hasTrace_3629_ = leanh::lean_ctor_get_uint8(
                    v_o_3625_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3643_ = (!leanh::lean_is_exclusive(v_o_3625_)) as u8;
                if v_isSharedCheck_3643_ == 0 {
                    v___x_3631_ = v_o_3625_;
                    v_isShared_3632_ = v_isSharedCheck_3643_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_3628_);
                    leanh::lean_dec(v_o_3625_);
                    v___x_3631_ = leanh::lean_box(0);
                    v_isShared_3632_ = v_isSharedCheck_3643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3633_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3633_, 0, v_v_3627_);
                leanh::lean_inc(v_k_3626_);
                v___x_3634_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3626_, v___x_3633_, v_map_3628_);
                if v_hasTrace_3629_ == 0 {
                    v___x_3635_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1;
                    v___x_3636_ = l_Lean_Name_isPrefixOf(v___x_3635_, v_k_3626_);
                    leanh::lean_dec(v_k_3626_);
                    if v_isShared_3632_ == 0 {
                        leanh::lean_ctor_set(v___x_3631_, 0, v___x_3634_);
                        v___x_3638_ = v___x_3631_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3639_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3634_);
                        v___x_3638_ = v_reuseFailAlloc_3639_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_3626_);
                    if v_isShared_3632_ == 0 {
                        leanh::lean_ctor_set(v___x_3631_, 0, v___x_3634_);
                        v___x_3641_ = v___x_3631_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3642_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3634_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_3642_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_3629_,
                        );
                        v___x_3641_ = v_reuseFailAlloc_3642_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3638_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3636_,
                );
                return v___x_3638_;
            }
            3 => {
                return v___x_3641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__2(
    mut v_o_3644_: *mut leanh::LeanObject,
    mut v_k_3645_: *mut leanh::LeanObject,
    mut v_v_3646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3648_: u8 = 0;
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3651_: u8 = 0;
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: u8 = 0;
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3647_ = leanh::lean_ctor_get(v_o_3644_, 0);
                v_hasTrace_3648_ = leanh::lean_ctor_get_uint8(
                    v_o_3644_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3662_ = (!leanh::lean_is_exclusive(v_o_3644_)) as u8;
                if v_isSharedCheck_3662_ == 0 {
                    v___x_3650_ = v_o_3644_;
                    v_isShared_3651_ = v_isSharedCheck_3662_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_3647_);
                    leanh::lean_dec(v_o_3644_);
                    v___x_3650_ = leanh::lean_box(0);
                    v_isShared_3651_ = v_isSharedCheck_3662_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3652_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3652_, 0, v_v_3646_);
                leanh::lean_inc(v_k_3645_);
                v___x_3653_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3645_, v___x_3652_, v_map_3647_);
                if v_hasTrace_3648_ == 0 {
                    v___x_3654_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1;
                    v___x_3655_ = l_Lean_Name_isPrefixOf(v___x_3654_, v_k_3645_);
                    leanh::lean_dec(v_k_3645_);
                    if v_isShared_3651_ == 0 {
                        leanh::lean_ctor_set(v___x_3650_, 0, v___x_3653_);
                        v___x_3657_ = v___x_3650_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3658_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3653_);
                        v___x_3657_ = v_reuseFailAlloc_3658_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_3645_);
                    if v_isShared_3651_ == 0 {
                        leanh::lean_ctor_set(v___x_3650_, 0, v___x_3653_);
                        v___x_3660_ = v___x_3650_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3661_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3653_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_3661_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_3648_,
                        );
                        v___x_3660_ = v_reuseFailAlloc_3661_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3657_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3655_,
                );
                return v___x_3657_;
            }
            3 => {
                return v___x_3660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_Lean_setOption(
    mut v_opts_3670_: *mut leanh::LeanObject,
    mut v_decl_3671_: *mut leanh::LeanObject,
    mut v_name_3672_: *mut leanh::LeanObject,
    mut v_val_3673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: u8 = 0;
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: u8 = 0;
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3692_: u8 = 0;
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3700_: u8 = 0;
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3705_: u8 = 0;
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3714_: u8 = 0;
    let mut v_unused_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3718_: u8 = 0;
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3723_: u8 = 0;
    let mut v_unused_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3675_ = leanh::lean_ctor_get(v_decl_3671_, 2);
                leanh::lean_inc_ref(v_defValue_3675_);
                leanh::lean_dec_ref(v_decl_3671_);
                match leanh::lean_obj_tag(v_defValue_3675_) {
                    1 => {
                        leanh::lean_dec_ref_known(v_defValue_3675_, 0);
                        v___x_3676_ = l_Lean_Language_Lean_setOption___closed__0;
                        v___x_3677_ = lean_string_dec_eq(v_val_3673_, v___x_3676_);
                        if v___x_3677_ == 0 {
                            v___x_3678_ = l_Lean_Language_Lean_setOption___closed__1;
                            v___x_3679_ = lean_string_dec_eq(v_val_3673_, v___x_3678_);
                            if v___x_3679_ == 0 {
                                leanh::lean_dec(v_name_3672_);
                                leanh::lean_dec_ref(v_opts_3670_);
                                v___x_3680_ = l_Lean_Language_Lean_setOption___closed__2;
                                v___x_3681_ = lean_string_append(v___x_3680_, v_val_3673_);
                                leanh::lean_dec_ref(v_val_3673_);
                                v___x_3682_ = l_Lean_Language_Lean_setOption___closed__3;
                                v___x_3683_ = lean_string_append(v___x_3681_, v___x_3682_);
                                v___x_3684_ = leanh::lean_alloc_ctor(18, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3684_, 0, v___x_3683_);
                                v___x_3685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3685_, 0, v___x_3684_);
                                return v___x_3685_;
                            } else {
                                leanh::lean_dec_ref(v_val_3673_);
                                v___x_3686_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_opts_3670_, v_name_3672_, v___x_3677_);
                                v___x_3687_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3687_, 0, v___x_3686_);
                                return v___x_3687_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_val_3673_);
                            v___x_3688_ =
                                l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(
                                    v_opts_3670_,
                                    v_name_3672_,
                                    v___x_3677_,
                                );
                            v___x_3689_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3689_, 0, v___x_3688_);
                            return v___x_3689_;
                        }
                    }
                    3 => {
                        v_isSharedCheck_3714_ =
                            (!leanh::lean_is_exclusive(v_defValue_3675_)) as u8;
                        if v_isSharedCheck_3714_ == 0 {
                            v_unused_3715_ = leanh::lean_ctor_get(v_defValue_3675_, 0);
                            leanh::lean_dec(v_unused_3715_);
                            v___x_3691_ = v_defValue_3675_;
                            v_isShared_3692_ = v_isSharedCheck_3714_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_defValue_3675_);
                            v___x_3691_ = leanh::lean_box(0);
                            v_isShared_3692_ = v_isSharedCheck_3714_;
                            state = 1;
                            continue;
                        }
                    }
                    0 => {
                        v_isSharedCheck_3723_ =
                            (!leanh::lean_is_exclusive(v_defValue_3675_)) as u8;
                        if v_isSharedCheck_3723_ == 0 {
                            v_unused_3724_ = leanh::lean_ctor_get(v_defValue_3675_, 0);
                            leanh::lean_dec(v_unused_3724_);
                            v___x_3717_ = v_defValue_3675_;
                            v_isShared_3718_ = v_isSharedCheck_3723_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v_defValue_3675_);
                            v___x_3717_ = leanh::lean_box(0);
                            v_isShared_3718_ = v_isSharedCheck_3723_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec_ref(v_defValue_3675_);
                        leanh::lean_dec_ref(v_val_3673_);
                        leanh::lean_dec_ref(v_opts_3670_);
                        v___x_3725_ = l_Lean_Language_Lean_setOption___closed__5;
                        v___x_3726_ = 1;
                        v___x_3727_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_3672_,
                                v___x_3726_,
                            );
                        v___x_3728_ = lean_string_append(v___x_3725_, v___x_3727_);
                        leanh::lean_dec_ref(v___x_3727_);
                        v___x_3729_ = l_Lean_Language_Lean_setOption___closed__6;
                        v___x_3730_ = lean_string_append(v___x_3728_, v___x_3729_);
                        v___x_3731_ = leanh::lean_alloc_ctor(18, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3731_, 0, v___x_3730_);
                        v___x_3732_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3732_, 0, v___x_3731_);
                        return v___x_3732_;
                    }
                }
            }
            1 => {
                v___x_3693_ = leanh::lean_unsigned_to_nat(0);
                v___x_3694_ = lean_string_utf8_byte_size(v_val_3673_);
                leanh::lean_inc_ref(v_val_3673_);
                v___x_3695_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3695_, 0, v_val_3673_);
                leanh::lean_ctor_set(v___x_3695_, 1, v___x_3693_);
                leanh::lean_ctor_set(v___x_3695_, 2, v___x_3694_);
                v___x_3696_ = l_String_Slice_toNat_x3f(v___x_3695_);
                leanh::lean_dec_ref_known(v___x_3695_, 3);
                if leanh::lean_obj_tag(v___x_3696_) == 1 {
                    leanh::lean_del_object(v___x_3691_);
                    leanh::lean_dec_ref(v_val_3673_);
                    v_val_3697_ = leanh::lean_ctor_get(v___x_3696_, 0);
                    v_isSharedCheck_3705_ = (!leanh::lean_is_exclusive(v___x_3696_)) as u8;
                    if v_isSharedCheck_3705_ == 0 {
                        v___x_3699_ = v___x_3696_;
                        v_isShared_3700_ = v_isSharedCheck_3705_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3697_);
                        leanh::lean_dec(v___x_3696_);
                        v___x_3699_ = leanh::lean_box(0);
                        v_isShared_3700_ = v_isSharedCheck_3705_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3696_);
                    leanh::lean_dec(v_name_3672_);
                    leanh::lean_dec_ref(v_opts_3670_);
                    v___x_3706_ = l_Lean_Language_Lean_setOption___closed__2;
                    v___x_3707_ = lean_string_append(v___x_3706_, v_val_3673_);
                    leanh::lean_dec_ref(v_val_3673_);
                    v___x_3708_ = l_Lean_Language_Lean_setOption___closed__4;
                    v___x_3709_ = lean_string_append(v___x_3707_, v___x_3708_);
                    if v_isShared_3692_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3691_, 18);
                        leanh::lean_ctor_set(v___x_3691_, 0, v___x_3709_);
                        v___x_3711_ = v___x_3691_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3713_ = leanh::lean_alloc_ctor(18, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3709_);
                        v___x_3711_ = v_reuseFailAlloc_3713_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3701_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__1(
                    v_opts_3670_,
                    v_name_3672_,
                    v_val_3697_,
                );
                if v_isShared_3700_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3699_, 0);
                    leanh::lean_ctor_set(v___x_3699_, 0, v___x_3701_);
                    v___x_3703_ = v___x_3699_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3704_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3701_);
                    v___x_3703_ = v_reuseFailAlloc_3704_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3703_;
            }
            4 => {
                v___x_3712_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3712_, 0, v___x_3711_);
                return v___x_3712_;
            }
            5 => {
                v___x_3719_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__2(
                    v_opts_3670_,
                    v_name_3672_,
                    v_val_3673_,
                );
                if v_isShared_3718_ == 0 {
                    leanh::lean_ctor_set(v___x_3717_, 0, v___x_3719_);
                    v___x_3721_ = v___x_3717_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3722_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3719_);
                    v___x_3721_ = v_reuseFailAlloc_3722_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_Lean_setOption___boxed(
    mut v_opts_3733_: *mut leanh::LeanObject,
    mut v_decl_3734_: *mut leanh::LeanObject,
    mut v_name_3735_: *mut leanh::LeanObject,
    mut v_val_3736_: *mut leanh::LeanObject,
    mut v_a_3737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3738_ =
        l_Lean_Language_Lean_setOption(v_opts_3733_, v_decl_3734_, v_name_3735_, v_val_3736_);
    return v_res_3738_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(
    mut v_o_3739_: *mut leanh::LeanObject,
    mut v_k_3740_: *mut leanh::LeanObject,
    mut v_v_3741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3743_: u8 = 0;
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3746_: u8 = 0;
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3742_ = leanh::lean_ctor_get(v_o_3739_, 0);
                v_hasTrace_3743_ = leanh::lean_ctor_get_uint8(
                    v_o_3739_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3756_ = (!leanh::lean_is_exclusive(v_o_3739_)) as u8;
                if v_isSharedCheck_3756_ == 0 {
                    v___x_3745_ = v_o_3739_;
                    v_isShared_3746_ = v_isSharedCheck_3756_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_3742_);
                    leanh::lean_dec(v_o_3739_);
                    v___x_3745_ = leanh::lean_box(0);
                    v_isShared_3746_ = v_isSharedCheck_3756_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_k_3740_);
                v___x_3747_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3740_, v_v_3741_, v_map_3742_);
                if v_hasTrace_3743_ == 0 {
                    v___x_3748_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1;
                    v___x_3749_ = l_Lean_Name_isPrefixOf(v___x_3748_, v_k_3740_);
                    leanh::lean_dec(v_k_3740_);
                    if v_isShared_3746_ == 0 {
                        leanh::lean_ctor_set(v___x_3745_, 0, v___x_3747_);
                        v___x_3751_ = v___x_3745_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3752_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3747_);
                        v___x_3751_ = v_reuseFailAlloc_3752_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_3740_);
                    if v_isShared_3746_ == 0 {
                        leanh::lean_ctor_set(v___x_3745_, 0, v___x_3747_);
                        v___x_3754_ = v___x_3745_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3755_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3747_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_3755_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_3743_,
                        );
                        v___x_3754_ = v_reuseFailAlloc_3755_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3751_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3749_,
                );
                return v___x_3751_;
            }
            3 => {
                return v___x_3754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(
    mut v_a_3763_: *mut leanh::LeanObject,
    mut v_init_3764_: *mut leanh::LeanObject,
    mut v_x_3765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_d_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3781_: u8 = 0;
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3795_: u8 = 0;
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3799_: u8 = 0;
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: u8 = 0;
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3805_: u8 = 0;
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: u8 = 0;
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3823_: u8 = 0;
    let mut v_unused_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3829_: u8 = 0;
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3765_) == 0 {
                    v_k_3771_ = leanh::lean_ctor_get(v_x_3765_, 1);
                    leanh::lean_inc(v_k_3771_);
                    v_v_3772_ = leanh::lean_ctor_get(v_x_3765_, 2);
                    leanh::lean_inc(v_v_3772_);
                    v_l_3773_ = leanh::lean_ctor_get(v_x_3765_, 3);
                    leanh::lean_inc(v_l_3773_);
                    v_r_3774_ = leanh::lean_ctor_get(v_x_3765_, 4);
                    leanh::lean_inc(v_r_3774_);
                    leanh::lean_dec_ref_known(v_x_3765_, 5);
                    v___x_3775_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_3763_, v_init_3764_, v_l_3773_);
                    if leanh::lean_obj_tag(v___x_3775_) == 0 {
                        v_a_3776_ = leanh::lean_ctor_get(v___x_3775_, 0);
                        leanh::lean_inc(v_a_3776_);
                        if leanh::lean_obj_tag(v_a_3776_) == 0 {
                            leanh::lean_dec_ref_known(v___x_3775_, 1);
                            leanh::lean_dec(v_r_3774_);
                            leanh::lean_dec(v_v_3772_);
                            leanh::lean_dec(v_k_3771_);
                            v_a_3777_ = leanh::lean_ctor_get(v_a_3776_, 0);
                            leanh::lean_inc(v_a_3777_);
                            leanh::lean_dec_ref_known(v_a_3776_, 1);
                            v_d_3768_ = v_a_3777_;
                            state = 1;
                            continue;
                        } else {
                            v_a_3778_ = leanh::lean_ctor_get(v_a_3776_, 0);
                            v_isSharedCheck_3829_ =
                                (!leanh::lean_is_exclusive(v_a_3776_)) as u8;
                            if v_isSharedCheck_3829_ == 0 {
                                v___x_3780_ = v_a_3776_;
                                v_isShared_3781_ = v_isSharedCheck_3829_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3778_);
                                leanh::lean_dec(v_a_3776_);
                                v___x_3780_ = leanh::lean_box(0);
                                v_isShared_3781_ = v_isSharedCheck_3829_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_r_3774_);
                        leanh::lean_dec(v_v_3772_);
                        leanh::lean_dec(v_k_3771_);
                        return v___x_3775_;
                    }
                } else {
                    v___x_3830_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3830_, 0, v_init_3764_);
                    v___x_3831_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3831_, 0, v___x_3830_);
                    return v___x_3831_;
                }
            }
            1 => {
                v___x_3769_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3769_, 0, v_d_3768_);
                v___x_3770_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3770_, 0, v___x_3769_);
                return v___x_3770_;
            }
            2 => {
                v___x_3782_ = l_Lean_Name_getRoot(v_k_3771_);
                v___x_3783_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__1;
                v___x_3784_ = leanh::lean_box(0);
                v___x_3785_ = l_Lean_Name_replacePrefix(v_k_3771_, v___x_3783_, v___x_3784_);
                v___x_3786_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_3763_, v___x_3785_);
                if leanh::lean_obj_tag(v___x_3786_) == 1 {
                    leanh::lean_dec(v___x_3782_);
                    leanh::lean_del_object(v___x_3780_);
                    leanh::lean_dec_ref_known(v___x_3775_, 1);
                    if leanh::lean_obj_tag(v_v_3772_) == 0 {
                        v_val_3787_ = leanh::lean_ctor_get(v___x_3786_, 0);
                        leanh::lean_inc(v_val_3787_);
                        leanh::lean_dec_ref_known(v___x_3786_, 1);
                        v_v_3788_ = leanh::lean_ctor_get(v_v_3772_, 0);
                        leanh::lean_inc_ref(v_v_3788_);
                        leanh::lean_dec_ref_known(v_v_3772_, 1);
                        v___x_3789_ = l_Lean_Language_Lean_setOption(
                            v_a_3778_,
                            v_val_3787_,
                            v___x_3785_,
                            v_v_3788_,
                        );
                        if leanh::lean_obj_tag(v___x_3789_) == 0 {
                            v_a_3790_ = leanh::lean_ctor_get(v___x_3789_, 0);
                            leanh::lean_inc(v_a_3790_);
                            leanh::lean_dec_ref_known(v___x_3789_, 1);
                            v_init_3764_ = v_a_3790_;
                            v_x_3765_ = v_r_3774_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_r_3774_);
                            v_a_3792_ = leanh::lean_ctor_get(v___x_3789_, 0);
                            v_isSharedCheck_3799_ =
                                (!leanh::lean_is_exclusive(v___x_3789_)) as u8;
                            if v_isSharedCheck_3799_ == 0 {
                                v___x_3794_ = v___x_3789_;
                                v_isShared_3795_ = v_isSharedCheck_3799_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3792_);
                                leanh::lean_dec(v___x_3789_);
                                v___x_3794_ = leanh::lean_box(0);
                                v_isShared_3795_ = v_isSharedCheck_3799_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_3786_, 1);
                        v___x_3800_ =
                            l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(
                                v_a_3778_,
                                v___x_3785_,
                                v_v_3772_,
                            );
                        v_init_3764_ = v___x_3800_;
                        v_x_3765_ = v_r_3774_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3786_);
                    leanh::lean_dec(v_a_3778_);
                    leanh::lean_dec(v_v_3772_);
                    v___x_3802_ = lean_name_eq(v___x_3782_, v___x_3783_);
                    leanh::lean_dec(v___x_3782_);
                    if v___x_3802_ == 0 {
                        leanh::lean_dec(v_r_3774_);
                        v_isSharedCheck_3823_ =
                            (!leanh::lean_is_exclusive(v___x_3775_)) as u8;
                        if v_isSharedCheck_3823_ == 0 {
                            v_unused_3824_ = leanh::lean_ctor_get(v___x_3775_, 0);
                            leanh::lean_dec(v_unused_3824_);
                            v___x_3804_ = v___x_3775_;
                            v_isShared_3805_ = v_isSharedCheck_3823_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3775_);
                            v___x_3804_ = leanh::lean_box(0);
                            v_isShared_3805_ = v_isSharedCheck_3823_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3785_);
                        leanh::lean_del_object(v___x_3780_);
                        if leanh::lean_obj_tag(v___x_3775_) == 0 {
                            v_a_3825_ = leanh::lean_ctor_get(v___x_3775_, 0);
                            leanh::lean_inc(v_a_3825_);
                            leanh::lean_dec_ref_known(v___x_3775_, 1);
                            if leanh::lean_obj_tag(v_a_3825_) == 0 {
                                leanh::lean_dec(v_r_3774_);
                                v_a_3826_ = leanh::lean_ctor_get(v_a_3825_, 0);
                                leanh::lean_inc(v_a_3826_);
                                leanh::lean_dec_ref_known(v_a_3825_, 1);
                                v_d_3768_ = v_a_3826_;
                                state = 1;
                                continue;
                            } else {
                                v_a_3827_ = leanh::lean_ctor_get(v_a_3825_, 0);
                                leanh::lean_inc(v_a_3827_);
                                leanh::lean_dec_ref_known(v_a_3825_, 1);
                                v_init_3764_ = v_a_3827_;
                                v_x_3765_ = v_r_3774_;
                                state = 0;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_r_3774_);
                            return v___x_3775_;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_3795_ == 0 {
                    v___x_3797_ = v___x_3794_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3798_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
                    v___x_3797_ = v_reuseFailAlloc_3798_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3797_;
            }
            5 => {
                v___x_3806_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__2;
                v___x_3807_ = 1;
                leanh::lean_inc(v___x_3785_);
                v___x_3808_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_3785_,
                    v___x_3807_,
                );
                v___x_3809_ = lean_string_append(v___x_3806_, v___x_3808_);
                leanh::lean_dec_ref(v___x_3808_);
                v___x_3810_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__3;
                v___x_3811_ = lean_string_append(v___x_3809_, v___x_3810_);
                v___x_3812_ = l_Lean_Name_append(v___x_3783_, v___x_3785_);
                v___x_3813_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_3812_,
                    v___x_3807_,
                );
                v___x_3814_ = lean_string_append(v___x_3811_, v___x_3813_);
                leanh::lean_dec_ref(v___x_3813_);
                v___x_3815_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__4;
                v___x_3816_ = lean_string_append(v___x_3814_, v___x_3815_);
                if v_isShared_3781_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3780_, 18);
                    leanh::lean_ctor_set(v___x_3780_, 0, v___x_3816_);
                    v___x_3818_ = v___x_3780_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3822_ = leanh::lean_alloc_ctor(18, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3816_);
                    v___x_3818_ = v_reuseFailAlloc_3822_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3805_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3804_, 1);
                    leanh::lean_ctor_set(v___x_3804_, 0, v___x_3818_);
                    v___x_3820_ = v___x_3804_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3821_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3818_);
                    v___x_3820_ = v_reuseFailAlloc_3821_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3820_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___boxed(
    mut v_a_3832_: *mut leanh::LeanObject,
    mut v_init_3833_: *mut leanh::LeanObject,
    mut v_x_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3836_ =
        l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(
            v_a_3832_,
            v_init_3833_,
            v_x_3834_,
        );
    leanh::lean_dec(v_a_3832_);
    return v_res_3836_;
}
pub unsafe fn l_Lean_Language_Lean_reparseOptions(
    mut v_opts_3837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_x27_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v_a_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut v_a_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3856_: u8 = 0;
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3860_: u8 = 0;
    let mut v_a_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3864_: u8 = 0;
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3868_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3839_ = l_Lean_getOptionDecls();
                if leanh::lean_obj_tag(v___x_3839_) == 0 {
                    v_a_3840_ = leanh::lean_ctor_get(v___x_3839_, 0);
                    leanh::lean_inc(v_a_3840_);
                    leanh::lean_dec_ref_known(v___x_3839_, 1);
                    v_map_3841_ = leanh::lean_ctor_get(v_opts_3837_, 0);
                    leanh::lean_inc(v_map_3841_);
                    leanh::lean_dec_ref(v_opts_3837_);
                    v_opts_x27_3842_ = l_Lean_Options_empty;
                    v___x_3843_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_3840_, v_opts_x27_3842_, v_map_3841_);
                    leanh::lean_dec(v_a_3840_);
                    if leanh::lean_obj_tag(v___x_3843_) == 0 {
                        v_a_3844_ = leanh::lean_ctor_get(v___x_3843_, 0);
                        v_isSharedCheck_3852_ =
                            (!leanh::lean_is_exclusive(v___x_3843_)) as u8;
                        if v_isSharedCheck_3852_ == 0 {
                            v___x_3846_ = v___x_3843_;
                            v_isShared_3847_ = v_isSharedCheck_3852_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3844_);
                            leanh::lean_dec(v___x_3843_);
                            v___x_3846_ = leanh::lean_box(0);
                            v_isShared_3847_ = v_isSharedCheck_3852_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3853_ = leanh::lean_ctor_get(v___x_3843_, 0);
                        v_isSharedCheck_3860_ =
                            (!leanh::lean_is_exclusive(v___x_3843_)) as u8;
                        if v_isSharedCheck_3860_ == 0 {
                            v___x_3855_ = v___x_3843_;
                            v_isShared_3856_ = v_isSharedCheck_3860_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3853_);
                            leanh::lean_dec(v___x_3843_);
                            v___x_3855_ = leanh::lean_box(0);
                            v_isShared_3856_ = v_isSharedCheck_3860_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_opts_3837_);
                    v_a_3861_ = leanh::lean_ctor_get(v___x_3839_, 0);
                    v_isSharedCheck_3868_ = (!leanh::lean_is_exclusive(v___x_3839_)) as u8;
                    if v_isSharedCheck_3868_ == 0 {
                        v___x_3863_ = v___x_3839_;
                        v_isShared_3864_ = v_isSharedCheck_3868_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3861_);
                        leanh::lean_dec(v___x_3839_);
                        v___x_3863_ = leanh::lean_box(0);
                        v_isShared_3864_ = v_isSharedCheck_3868_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3848_ = leanh::lean_ctor_get(v_a_3844_, 0);
                leanh::lean_inc(v_a_3848_);
                leanh::lean_dec(v_a_3844_);
                if v_isShared_3847_ == 0 {
                    leanh::lean_ctor_set(v___x_3846_, 0, v_a_3848_);
                    v___x_3850_ = v___x_3846_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3851_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3848_);
                    v___x_3850_ = v_reuseFailAlloc_3851_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3850_;
            }
            3 => {
                if v_isShared_3856_ == 0 {
                    v___x_3858_ = v___x_3855_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3859_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
                    v___x_3858_ = v_reuseFailAlloc_3859_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3858_;
            }
            5 => {
                if v_isShared_3864_ == 0 {
                    v___x_3866_ = v___x_3863_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3867_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
                    v___x_3866_ = v_reuseFailAlloc_3867_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3866_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_Lean_reparseOptions___boxed(
    mut v_opts_3869_: *mut leanh::LeanObject,
    mut v_a_3870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3871_ = l_Lean_Language_Lean_reparseOptions(v_opts_3869_);
    return v_res_3871_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(
    mut v_stx_3880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stx_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: u8 = 0;
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: u8 = 0;
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3885_ = leanh::lean_unsigned_to_nat(0);
                v___x_3886_ = l_Lean_Syntax_getArg(v_stx_3880_, v___x_3885_);
                v___x_3887_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3;
                v___x_3888_ = l_Lean_Syntax_isOfKind(v___x_3886_, v___x_3887_);
                if v___x_3888_ == 0 {
                    v_stx_3882_ = v_stx_3880_;
                    state = 1;
                    continue;
                } else {
                    v___x_3889_ = leanh::lean_unsigned_to_nat(1);
                    v_stx_3890_ = l_Lean_Syntax_getArg(v_stx_3880_, v___x_3889_);
                    leanh::lean_dec(v_stx_3880_);
                    v_stx_3882_ = v_stx_3890_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3883_ = 0;
                v___x_3884_ = l_Lean_Syntax_getPos_x3f(v_stx_3882_, v___x_3883_);
                leanh::lean_dec(v_stx_3882_);
                return v___x_3884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(
    mut v_name_3891_: *mut leanh::LeanObject,
    mut v_decl_3892_: *mut leanh::LeanObject,
    mut v_ref_3893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: u8 = 0;
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3904_: u8 = 0;
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3909_: u8 = 0;
    let mut v_unused_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3895_ = leanh::lean_ctor_get(v_decl_3892_, 0);
                v_descr_3896_ = leanh::lean_ctor_get(v_decl_3892_, 1);
                v_deprecation_x3f_3897_ = leanh::lean_ctor_get(v_decl_3892_, 2);
                v___x_3898_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3899_ = (leanh::lean_unbox(v_defValue_3895_) as u8);
                leanh::lean_ctor_set_uint8(v___x_3898_, 0 as u32, v___x_3899_);
                leanh::lean_inc(v_deprecation_x3f_3897_);
                leanh::lean_inc_ref(v_descr_3896_);
                leanh::lean_inc_n(v_name_3891_, 2);
                v___x_3900_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_3900_, 0, v_name_3891_);
                leanh::lean_ctor_set(v___x_3900_, 1, v_ref_3893_);
                leanh::lean_ctor_set(v___x_3900_, 2, v___x_3898_);
                leanh::lean_ctor_set(v___x_3900_, 3, v_descr_3896_);
                leanh::lean_ctor_set(v___x_3900_, 4, v_deprecation_x3f_3897_);
                v___x_3901_ = lean_register_option(v_name_3891_, v___x_3900_);
                if leanh::lean_obj_tag(v___x_3901_) == 0 {
                    v_isSharedCheck_3909_ = (!leanh::lean_is_exclusive(v___x_3901_)) as u8;
                    if v_isSharedCheck_3909_ == 0 {
                        v_unused_3910_ = leanh::lean_ctor_get(v___x_3901_, 0);
                        leanh::lean_dec(v_unused_3910_);
                        v___x_3903_ = v___x_3901_;
                        v_isShared_3904_ = v_isSharedCheck_3909_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3901_);
                        v___x_3903_ = leanh::lean_box(0);
                        v_isShared_3904_ = v_isSharedCheck_3909_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_3891_);
                    v_a_3911_ = leanh::lean_ctor_get(v___x_3901_, 0);
                    v_isSharedCheck_3918_ = (!leanh::lean_is_exclusive(v___x_3901_)) as u8;
                    if v_isSharedCheck_3918_ == 0 {
                        v___x_3913_ = v___x_3901_;
                        v_isShared_3914_ = v_isSharedCheck_3918_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3911_);
                        leanh::lean_dec(v___x_3901_);
                        v___x_3913_ = leanh::lean_box(0);
                        v_isShared_3914_ = v_isSharedCheck_3918_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_3895_);
                v___x_3905_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3905_, 0, v_name_3891_);
                leanh::lean_ctor_set(v___x_3905_, 1, v_defValue_3895_);
                if v_isShared_3904_ == 0 {
                    leanh::lean_ctor_set(v___x_3903_, 0, v___x_3905_);
                    v___x_3907_ = v___x_3903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3908_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3905_);
                    v___x_3907_ = v_reuseFailAlloc_3908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3907_;
            }
            3 => {
                if v_isShared_3914_ == 0 {
                    v___x_3916_ = v___x_3913_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3917_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
                    v___x_3916_ = v_reuseFailAlloc_3917_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3916_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_3919_: *mut leanh::LeanObject,
    mut v_decl_3920_: *mut leanh::LeanObject,
    mut v_ref_3921_: *mut leanh::LeanObject,
    mut v_a_3922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3923_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v_name_3919_, v_decl_3920_, v_ref_3921_);
    leanh::lean_dec_ref(v_decl_3920_);
    return v_res_3923_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3941_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_;
    v___x_3942_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_;
    v___x_3943_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_;
    v___x_3944_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v___x_3941_, v___x_3942_, v___x_3943_);
    return v___x_3944_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4____boxed(
    mut v_a_3945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3946_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
    return v_res_3946_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3947_ = leanh::lean_unsigned_to_nat(32);
    v___x_3948_ = lean_mk_empty_array_with_capacity(v___x_3947_);
    v___x_3949_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3949_, 0, v___x_3948_);
    return v___x_3949_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3950_: usize = 0;
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3950_ = 5usize;
    v___x_3951_ = leanh::lean_unsigned_to_nat(0);
    v___x_3952_ = leanh::lean_unsigned_to_nat(32);
    v___x_3953_ = lean_mk_empty_array_with_capacity(v___x_3952_);
    v___x_3954_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0);
    v___x_3955_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3955_, 0, v___x_3954_);
    leanh::lean_ctor_set(v___x_3955_, 1, v___x_3953_);
    leanh::lean_ctor_set(v___x_3955_, 2, v___x_3951_);
    leanh::lean_ctor_set(v___x_3955_, 3, v___x_3951_);
    leanh::lean_ctor_set_usize(v___x_3955_, 4, v___x_3950_);
    return v___x_3955_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(
    mut v___y_3956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3975_: u8 = 0;
    let mut v_enabled_3976_: u8 = 0;
    let mut v_assignment_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3981_: u8 = 0;
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3991_: u8 = 0;
    let mut v_unused_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3958_ = lean_st_ref_get(v___y_3956_);
                v_infoState_3959_ = leanh::lean_ctor_get(v___x_3958_, 8);
                leanh::lean_inc_ref(v_infoState_3959_);
                leanh::lean_dec(v___x_3958_);
                v_trees_3960_ = leanh::lean_ctor_get(v_infoState_3959_, 2);
                leanh::lean_inc_ref(v_trees_3960_);
                leanh::lean_dec_ref(v_infoState_3959_);
                v___x_3961_ = lean_st_ref_take(v___y_3956_);
                v_infoState_3962_ = leanh::lean_ctor_get(v___x_3961_, 8);
                v_env_3963_ = leanh::lean_ctor_get(v___x_3961_, 0);
                v_messages_3964_ = leanh::lean_ctor_get(v___x_3961_, 1);
                v_scopes_3965_ = leanh::lean_ctor_get(v___x_3961_, 2);
                v_usedQuotCtxts_3966_ = leanh::lean_ctor_get(v___x_3961_, 3);
                v_nextMacroScope_3967_ = leanh::lean_ctor_get(v___x_3961_, 4);
                v_maxRecDepth_3968_ = leanh::lean_ctor_get(v___x_3961_, 5);
                v_ngen_3969_ = leanh::lean_ctor_get(v___x_3961_, 6);
                v_auxDeclNGen_3970_ = leanh::lean_ctor_get(v___x_3961_, 7);
                v_traceState_3971_ = leanh::lean_ctor_get(v___x_3961_, 9);
                v_snapshotTasks_3972_ = leanh::lean_ctor_get(v___x_3961_, 10);
                v_isSharedCheck_3993_ = (!leanh::lean_is_exclusive(v___x_3961_)) as u8;
                if v_isSharedCheck_3993_ == 0 {
                    v___x_3974_ = v___x_3961_;
                    v_isShared_3975_ = v_isSharedCheck_3993_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3972_);
                    leanh::lean_inc(v_traceState_3971_);
                    leanh::lean_inc(v_infoState_3962_);
                    leanh::lean_inc(v_auxDeclNGen_3970_);
                    leanh::lean_inc(v_ngen_3969_);
                    leanh::lean_inc(v_maxRecDepth_3968_);
                    leanh::lean_inc(v_nextMacroScope_3967_);
                    leanh::lean_inc(v_usedQuotCtxts_3966_);
                    leanh::lean_inc(v_scopes_3965_);
                    leanh::lean_inc(v_messages_3964_);
                    leanh::lean_inc(v_env_3963_);
                    leanh::lean_dec(v___x_3961_);
                    v___x_3974_ = leanh::lean_box(0);
                    v_isShared_3975_ = v_isSharedCheck_3993_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_3976_ = leanh::lean_ctor_get_uint8(
                    v_infoState_3962_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_3977_ = leanh::lean_ctor_get(v_infoState_3962_, 0);
                v_lazyAssignment_3978_ = leanh::lean_ctor_get(v_infoState_3962_, 1);
                v_isSharedCheck_3991_ = (!leanh::lean_is_exclusive(v_infoState_3962_)) as u8;
                if v_isSharedCheck_3991_ == 0 {
                    v_unused_3992_ = leanh::lean_ctor_get(v_infoState_3962_, 2);
                    leanh::lean_dec(v_unused_3992_);
                    v___x_3980_ = v_infoState_3962_;
                    v_isShared_3981_ = v_isSharedCheck_3991_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lazyAssignment_3978_);
                    leanh::lean_inc(v_assignment_3977_);
                    leanh::lean_dec(v_infoState_3962_);
                    v___x_3980_ = leanh::lean_box(0);
                    v_isShared_3981_ = v_isSharedCheck_3991_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3982_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1);
                if v_isShared_3981_ == 0 {
                    leanh::lean_ctor_set(v___x_3980_, 2, v___x_3982_);
                    v___x_3984_ = v___x_3980_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3990_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_assignment_3977_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 1, v_lazyAssignment_3978_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 2, v___x_3982_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3990_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_3976_,
                    );
                    v___x_3984_ = v_reuseFailAlloc_3990_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3975_ == 0 {
                    leanh::lean_ctor_set(v___x_3974_, 8, v___x_3984_);
                    v___x_3986_ = v___x_3974_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3989_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_env_3963_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 1, v_messages_3964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 2, v_scopes_3965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 3, v_usedQuotCtxts_3966_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 4, v_nextMacroScope_3967_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 5, v_maxRecDepth_3968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 6, v_ngen_3969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 7, v_auxDeclNGen_3970_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 8, v___x_3984_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 9, v_traceState_3971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 10, v_snapshotTasks_3972_);
                    v___x_3986_ = v_reuseFailAlloc_3989_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3987_ = lean_st_ref_set(v___y_3956_, v___x_3986_);
                v___x_3988_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3988_, 0, v_trees_3960_);
                return v___x_3988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___boxed(
    mut v___y_3994_: *mut leanh::LeanObject,
    mut v___y_3995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3996_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_3994_);
    leanh::lean_dec(v___y_3994_);
    return v_res_3996_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(
    mut v___y_3997_: *mut leanh::LeanObject,
    mut v___y_3998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4000_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_3998_);
    return v___x_4000_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___boxed(
    mut v___y_4001_: *mut leanh::LeanObject,
    mut v___y_4002_: *mut leanh::LeanObject,
    mut v___y_4003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4004_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(v___y_4001_, v___y_4002_);
    leanh::lean_dec(v___y_4002_);
    leanh::lean_dec_ref(v___y_4001_);
    return v_res_4004_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(
    mut v_opts_4005_: *mut leanh::LeanObject,
    mut v_opt_4006_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4007_ = leanh::lean_ctor_get(v_opt_4006_, 0);
    v_defValue_4008_ = leanh::lean_ctor_get(v_opt_4006_, 1);
    v_map_4009_ = leanh::lean_ctor_get(v_opts_4005_, 0);
    v___x_4010_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4009_,
            v_name_4007_,
        );
    if leanh::lean_obj_tag(v___x_4010_) == 0 {
        let mut v___x_4011_: u8 = 0;
        v___x_4011_ = (leanh::lean_unbox(v_defValue_4008_) as u8);
        return v___x_4011_;
    } else {
        let mut v_val_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4012_ = leanh::lean_ctor_get(v___x_4010_, 0);
        leanh::lean_inc(v_val_4012_);
        leanh::lean_dec_ref_known(v___x_4010_, 1);
        if leanh::lean_obj_tag(v_val_4012_) == 1 {
            let mut v_v_4013_: u8 = 0;
            v_v_4013_ = leanh::lean_ctor_get_uint8(v_val_4012_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_4012_, 0);
            return v_v_4013_;
        } else {
            let mut v___x_4014_: u8 = 0;
            leanh::lean_dec(v_val_4012_);
            v___x_4014_ = (leanh::lean_unbox(v_defValue_4008_) as u8);
            return v___x_4014_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1___boxed(
    mut v_opts_4015_: *mut leanh::LeanObject,
    mut v_opt_4016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4017_: u8 = 0;
    let mut v_r_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4017_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_4015_, v_opt_4016_);
    leanh::lean_dec_ref(v_opt_4016_);
    leanh::lean_dec_ref(v_opts_4015_);
    v_r_4018_ = leanh::lean_box((v_res_4017_) as usize);
    return v_r_4018_;
}
pub unsafe fn l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(
    mut v_val_4021_: *mut leanh::LeanObject,
    mut v_x_4022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4023_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0;
    v___x_4024_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4024_, 0, v_val_4021_);
    leanh::lean_ctor_set(v___x_4024_, 1, v___x_4023_);
    return v___x_4024_;
}
pub unsafe fn l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(
    mut v_inst_4025_: *mut leanh::LeanObject,
    mut v_val_4026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_val_4026_);
    v___f_4027_ = leanh::lean_alloc_closure(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0 as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_4027_, 0, v_val_4026_);
    v___x_4028_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4028_, 0, v_inst_4025_);
    leanh::lean_ctor_set(v___x_4028_, 1, v_val_4026_);
    v___x_4029_ = lean_mk_thunk(v___f_4027_);
    v___x_4030_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4030_, 0, v___x_4028_);
    leanh::lean_ctor_set(v___x_4030_, 1, v___x_4029_);
    return v___x_4030_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(
    mut v_stx_4031_: *mut leanh::LeanObject,
    mut v___y_4032_: *mut leanh::LeanObject,
    mut v___y_4033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4035_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_4033_);
    leanh::lean_dec_ref(v___x_4035_);
    v___x_4036_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_4031_, v___y_4032_, v___y_4033_);
    return v___x_4036_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(
    mut v_stx_4037_: *mut leanh::LeanObject,
    mut v___y_4038_: *mut leanh::LeanObject,
    mut v___y_4039_: *mut leanh::LeanObject,
    mut v___y_4040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4041_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(
        v_stx_4037_,
        v___y_4038_,
        v___y_4039_,
    );
    leanh::lean_dec(v___y_4039_);
    leanh::lean_dec_ref(v___y_4038_);
    return v_res_4041_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4042_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4042_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4043_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
    v___x_4044_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4044_, 0, v___x_4043_);
    return v___x_4044_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4045_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
    v___x_4046_ = leanh::lean_unsigned_to_nat(0);
    v___x_4047_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_4047_, 0, v___x_4046_);
    leanh::lean_ctor_set(v___x_4047_, 1, v___x_4046_);
    leanh::lean_ctor_set(v___x_4047_, 2, v___x_4046_);
    leanh::lean_ctor_set(v___x_4047_, 3, v___x_4046_);
    leanh::lean_ctor_set(v___x_4047_, 4, v___x_4045_);
    leanh::lean_ctor_set(v___x_4047_, 5, v___x_4045_);
    leanh::lean_ctor_set(v___x_4047_, 6, v___x_4045_);
    leanh::lean_ctor_set(v___x_4047_, 7, v___x_4045_);
    leanh::lean_ctor_set(v___x_4047_, 8, v___x_4045_);
    leanh::lean_ctor_set(v___x_4047_, 9, v___x_4045_);
    return v___x_4047_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4048_ = leanh::lean_unsigned_to_nat(32);
    v___x_4049_ = lean_mk_empty_array_with_capacity(v___x_4048_);
    v___x_4050_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4050_, 0, v___x_4049_);
    return v___x_4050_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4051_: usize = 0;
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4051_ = 5usize;
    v___x_4052_ = leanh::lean_unsigned_to_nat(0);
    v___x_4053_ = leanh::lean_unsigned_to_nat(32);
    v___x_4054_ = lean_mk_empty_array_with_capacity(v___x_4053_);
    v___x_4055_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
    v___x_4056_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_4056_, 0, v___x_4055_);
    leanh::lean_ctor_set(v___x_4056_, 1, v___x_4054_);
    leanh::lean_ctor_set(v___x_4056_, 2, v___x_4052_);
    leanh::lean_ctor_set(v___x_4056_, 3, v___x_4052_);
    leanh::lean_ctor_set_usize(v___x_4056_, 4, v___x_4051_);
    return v___x_4056_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4057_ = leanh::lean_box(1);
    v___x_4058_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
    v___x_4059_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
    v___x_4060_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4060_, 0, v___x_4059_);
    leanh::lean_ctor_set(v___x_4060_, 1, v___x_4058_);
    leanh::lean_ctor_set(v___x_4060_, 2, v___x_4057_);
    return v___x_4060_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(
    mut v_msgData_4061_: *mut leanh::LeanObject,
    mut v___y_4062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4064_ = lean_st_ref_get(v___y_4062_);
    v_env_4065_ = leanh::lean_ctor_get(v___x_4064_, 0);
    leanh::lean_inc_ref(v_env_4065_);
    leanh::lean_dec(v___x_4064_);
    v___x_4066_ = lean_st_ref_get(v___y_4062_);
    v_scopes_4067_ = leanh::lean_ctor_get(v___x_4066_, 2);
    leanh::lean_inc(v_scopes_4067_);
    leanh::lean_dec(v___x_4066_);
    v___x_4068_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_4069_ = l_List_head_x21___redArg(v___x_4068_, v_scopes_4067_);
    leanh::lean_dec(v_scopes_4067_);
    v_opts_4070_ = leanh::lean_ctor_get(v___x_4069_, 1);
    leanh::lean_inc_ref(v_opts_4070_);
    leanh::lean_dec(v___x_4069_);
    v___x_4071_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
    v___x_4072_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
    v___x_4073_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4073_, 0, v_env_4065_);
    leanh::lean_ctor_set(v___x_4073_, 1, v___x_4071_);
    leanh::lean_ctor_set(v___x_4073_, 2, v___x_4072_);
    leanh::lean_ctor_set(v___x_4073_, 3, v_opts_4070_);
    v___x_4074_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4074_, 0, v___x_4073_);
    leanh::lean_ctor_set(v___x_4074_, 1, v_msgData_4061_);
    v___x_4075_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4075_, 0, v___x_4074_);
    return v___x_4075_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(
    mut v_msgData_4076_: *mut leanh::LeanObject,
    mut v___y_4077_: *mut leanh::LeanObject,
    mut v___y_4078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4079_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_4076_, v___y_4077_);
    leanh::lean_dec(v___y_4077_);
    return v_res_4079_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(
    mut v___y_4080_: u8,
    mut v_suppressElabErrors_4081_: u8,
    mut v_x_4082_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4082_) == 1 {
        let mut v_pre_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_4083_ = leanh::lean_ctor_get(v_x_4082_, 0);
        if leanh::lean_obj_tag(v_pre_4083_) == 0 {
            let mut v_str_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4086_: u8 = 0;
            v_str_4084_ = leanh::lean_ctor_get(v_x_4082_, 1);
            v___x_4085_ =
                l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0;
            v___x_4086_ = lean_string_dec_eq(v_str_4084_, v___x_4085_);
            if v___x_4086_ == 0 {
                return v___y_4080_;
            } else {
                return v_suppressElabErrors_4081_;
            }
        } else {
            return v___y_4080_;
        }
    } else {
        return v___y_4080_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(
    mut v___y_4087_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_4088_: *mut leanh::LeanObject,
    mut v_x_4089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_9164__boxed_4090_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4091_: u8 = 0;
    let mut v_res_4092_: u8 = 0;
    let mut v_r_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_9164__boxed_4090_ = (leanh::lean_unbox(v___y_4087_) as u8);
    v_suppressElabErrors_boxed_4091_ = (leanh::lean_unbox(v_suppressElabErrors_4088_) as u8);
    v_res_4092_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v___y_9164__boxed_4090_, v_suppressElabErrors_boxed_4091_, v_x_4089_);
    leanh::lean_dec(v_x_4089_);
    v_r_4093_ = leanh::lean_box((v_res_4092_) as usize);
    return v_r_4093_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(
    mut v_ref_4095_: *mut leanh::LeanObject,
    mut v_msgData_4096_: *mut leanh::LeanObject,
    mut v_severity_4097_: u8,
    mut v_isSilent_4098_: u8,
    mut v___y_4099_: *mut leanh::LeanObject,
    mut v___y_4100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4104_: u8 = 0;
    let mut v___y_4105_: u8 = 0;
    let mut v___y_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4117_: u8 = 0;
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4134_: u8 = 0;
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4147_: u8 = 0;
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_a_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut v_a_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut v___y_4166_: u8 = 0;
    let mut v___y_4167_: u8 = 0;
    let mut v___y_4168_: u8 = 0;
    let mut v___y_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4173_: u8 = 0;
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4179_: u8 = 0;
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: u8 = 0;
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4192_: u8 = 0;
    let mut v___y_4194_: u8 = 0;
    let mut v___y_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4196_: u8 = 0;
    let mut v___y_4197_: u8 = 0;
    let mut v___y_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4202_: u8 = 0;
    let mut v___y_4203_: u8 = 0;
    let mut v___y_4204_: u8 = 0;
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4214_: u8 = 0;
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4218_: u8 = 0;
    let mut v___x_4219_: u8 = 0;
    let mut v___y_4221_: u8 = 0;
    let mut v___y_4222_: u8 = 0;
    let mut v___y_4223_: u8 = 0;
    let mut v___y_4225_: u8 = 0;
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: u8 = 0;
    let mut v___x_4232_: u8 = 0;
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: u8 = 0;
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: u8 = 0;
    let mut v___x_4238_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4219_ = 2;
                v___x_4237_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4097_, v___x_4219_);
                if v___x_4237_ == 0 {
                    v___y_4225_ = v___x_4237_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_4096_);
                    v___x_4238_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4096_);
                    v___y_4225_ = v___x_4238_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_4111_ = l_Lean_Elab_Command_getScope___redArg(v___y_4110_);
                if leanh::lean_obj_tag(v___x_4111_) == 0 {
                    v_a_4112_ = leanh::lean_ctor_get(v___x_4111_, 0);
                    leanh::lean_inc(v_a_4112_);
                    leanh::lean_dec_ref_known(v___x_4111_, 1);
                    v___x_4113_ = l_Lean_Elab_Command_getScope___redArg(v___y_4110_);
                    if leanh::lean_obj_tag(v___x_4113_) == 0 {
                        v_a_4114_ = leanh::lean_ctor_get(v___x_4113_, 0);
                        v_isSharedCheck_4148_ =
                            (!leanh::lean_is_exclusive(v___x_4113_)) as u8;
                        if v_isSharedCheck_4148_ == 0 {
                            v___x_4116_ = v___x_4113_;
                            v_isShared_4117_ = v_isSharedCheck_4148_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4114_);
                            leanh::lean_dec(v___x_4113_);
                            v___x_4116_ = leanh::lean_box(0);
                            v_isShared_4117_ = v_isSharedCheck_4148_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4112_);
                        leanh::lean_dec(v___y_4109_);
                        leanh::lean_dec_ref(v___y_4107_);
                        leanh::lean_dec_ref(v___y_4103_);
                        v_a_4149_ = leanh::lean_ctor_get(v___x_4113_, 0);
                        v_isSharedCheck_4156_ =
                            (!leanh::lean_is_exclusive(v___x_4113_)) as u8;
                        if v_isSharedCheck_4156_ == 0 {
                            v___x_4151_ = v___x_4113_;
                            v_isShared_4152_ = v_isSharedCheck_4156_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4149_);
                            leanh::lean_dec(v___x_4113_);
                            v___x_4151_ = leanh::lean_box(0);
                            v_isShared_4152_ = v_isSharedCheck_4156_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_4109_);
                    leanh::lean_dec_ref(v___y_4107_);
                    leanh::lean_dec_ref(v___y_4103_);
                    v_a_4157_ = leanh::lean_ctor_get(v___x_4111_, 0);
                    v_isSharedCheck_4164_ = (!leanh::lean_is_exclusive(v___x_4111_)) as u8;
                    if v_isSharedCheck_4164_ == 0 {
                        v___x_4159_ = v___x_4111_;
                        v_isShared_4160_ = v_isSharedCheck_4164_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4157_);
                        leanh::lean_dec(v___x_4111_);
                        v___x_4159_ = leanh::lean_box(0);
                        v_isShared_4160_ = v_isSharedCheck_4164_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4118_ = lean_st_ref_take(v___y_4110_);
                v_currNamespace_4119_ = leanh::lean_ctor_get(v_a_4112_, 2);
                leanh::lean_inc(v_currNamespace_4119_);
                leanh::lean_dec(v_a_4112_);
                v_openDecls_4120_ = leanh::lean_ctor_get(v_a_4114_, 3);
                leanh::lean_inc(v_openDecls_4120_);
                leanh::lean_dec(v_a_4114_);
                v_env_4121_ = leanh::lean_ctor_get(v___x_4118_, 0);
                v_messages_4122_ = leanh::lean_ctor_get(v___x_4118_, 1);
                v_scopes_4123_ = leanh::lean_ctor_get(v___x_4118_, 2);
                v_usedQuotCtxts_4124_ = leanh::lean_ctor_get(v___x_4118_, 3);
                v_nextMacroScope_4125_ = leanh::lean_ctor_get(v___x_4118_, 4);
                v_maxRecDepth_4126_ = leanh::lean_ctor_get(v___x_4118_, 5);
                v_ngen_4127_ = leanh::lean_ctor_get(v___x_4118_, 6);
                v_auxDeclNGen_4128_ = leanh::lean_ctor_get(v___x_4118_, 7);
                v_infoState_4129_ = leanh::lean_ctor_get(v___x_4118_, 8);
                v_traceState_4130_ = leanh::lean_ctor_get(v___x_4118_, 9);
                v_snapshotTasks_4131_ = leanh::lean_ctor_get(v___x_4118_, 10);
                v_isSharedCheck_4147_ = (!leanh::lean_is_exclusive(v___x_4118_)) as u8;
                if v_isSharedCheck_4147_ == 0 {
                    v___x_4133_ = v___x_4118_;
                    v_isShared_4134_ = v_isSharedCheck_4147_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4131_);
                    leanh::lean_inc(v_traceState_4130_);
                    leanh::lean_inc(v_infoState_4129_);
                    leanh::lean_inc(v_auxDeclNGen_4128_);
                    leanh::lean_inc(v_ngen_4127_);
                    leanh::lean_inc(v_maxRecDepth_4126_);
                    leanh::lean_inc(v_nextMacroScope_4125_);
                    leanh::lean_inc(v_usedQuotCtxts_4124_);
                    leanh::lean_inc(v_scopes_4123_);
                    leanh::lean_inc(v_messages_4122_);
                    leanh::lean_inc(v_env_4121_);
                    leanh::lean_dec(v___x_4118_);
                    v___x_4133_ = leanh::lean_box(0);
                    v_isShared_4134_ = v_isSharedCheck_4147_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4135_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4135_, 0, v_currNamespace_4119_);
                leanh::lean_ctor_set(v___x_4135_, 1, v_openDecls_4120_);
                v___x_4136_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4136_, 0, v___x_4135_);
                leanh::lean_ctor_set(v___x_4136_, 1, v___y_4103_);
                leanh::lean_inc_ref(v___y_4106_);
                leanh::lean_inc_ref(v___y_4108_);
                v___x_4137_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_4137_, 0, v___y_4108_);
                leanh::lean_ctor_set(v___x_4137_, 1, v___y_4107_);
                leanh::lean_ctor_set(v___x_4137_, 2, v___y_4109_);
                leanh::lean_ctor_set(v___x_4137_, 3, v___y_4106_);
                leanh::lean_ctor_set(v___x_4137_, 4, v___x_4136_);
                leanh::lean_ctor_set_uint8(
                    v___x_4137_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_4105_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4137_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_4104_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4137_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4098_,
                );
                v___x_4138_ = l_Lean_MessageLog_add(v___x_4137_, v_messages_4122_);
                if v_isShared_4134_ == 0 {
                    leanh::lean_ctor_set(v___x_4133_, 1, v___x_4138_);
                    v___x_4140_ = v___x_4133_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_env_4121_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 1, v___x_4138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 2, v_scopes_4123_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 3, v_usedQuotCtxts_4124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 4, v_nextMacroScope_4125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 5, v_maxRecDepth_4126_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 6, v_ngen_4127_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 7, v_auxDeclNGen_4128_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 8, v_infoState_4129_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 9, v_traceState_4130_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 10, v_snapshotTasks_4131_);
                    v___x_4140_ = v_reuseFailAlloc_4146_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4141_ = lean_st_ref_set(v___y_4110_, v___x_4140_);
                v___x_4142_ = leanh::lean_box(0);
                if v_isShared_4117_ == 0 {
                    leanh::lean_ctor_set(v___x_4116_, 0, v___x_4142_);
                    v___x_4144_ = v___x_4116_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4145_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4142_);
                    v___x_4144_ = v_reuseFailAlloc_4145_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4144_;
            }
            6 => {
                if v_isShared_4152_ == 0 {
                    v___x_4154_ = v___x_4151_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
                    v___x_4154_ = v_reuseFailAlloc_4155_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4154_;
            }
            8 => {
                if v_isShared_4160_ == 0 {
                    v___x_4162_ = v___x_4159_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4163_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
                    v___x_4162_ = v_reuseFailAlloc_4163_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4162_;
            }
            10 => {
                v_fileName_4171_ = leanh::lean_ctor_get(v___y_4099_, 0);
                v_fileMap_4172_ = leanh::lean_ctor_get(v___y_4099_, 1);
                v_suppressElabErrors_4173_ = leanh::lean_ctor_get_uint8(
                    v___y_4099_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                v___x_4174_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4096_,
                    );
                v___x_4175_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_4174_, v___y_4100_);
                v_a_4176_ = leanh::lean_ctor_get(v___x_4175_, 0);
                v_isSharedCheck_4192_ = (!leanh::lean_is_exclusive(v___x_4175_)) as u8;
                if v_isSharedCheck_4192_ == 0 {
                    v___x_4178_ = v___x_4175_;
                    v_isShared_4179_ = v_isSharedCheck_4192_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4176_);
                    leanh::lean_dec(v___x_4175_);
                    v___x_4178_ = leanh::lean_box(0);
                    v_isShared_4179_ = v_isSharedCheck_4192_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                leanh::lean_inc_ref_n(v_fileMap_4172_, 2);
                v___x_4180_ = l_Lean_FileMap_toPosition(v_fileMap_4172_, v___y_4169_);
                leanh::lean_dec(v___y_4169_);
                v___x_4181_ = l_Lean_FileMap_toPosition(v_fileMap_4172_, v___y_4170_);
                leanh::lean_dec(v___y_4170_);
                v___x_4182_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4182_, 0, v___x_4181_);
                v___x_4183_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0;
                if v_suppressElabErrors_4173_ == 0 {
                    leanh::lean_del_object(v___x_4178_);
                    v___y_4103_ = v_a_4176_;
                    v___y_4104_ = v___y_4168_;
                    v___y_4105_ = v___y_4167_;
                    v___y_4106_ = v___x_4183_;
                    v___y_4107_ = v___x_4180_;
                    v___y_4108_ = v_fileName_4171_;
                    v___y_4109_ = v___x_4182_;
                    v___y_4110_ = v___y_4100_;
                    state = 1;
                    continue;
                } else {
                    v___x_4184_ = leanh::lean_box((v___y_4166_) as usize);
                    v___x_4185_ = leanh::lean_box((v_suppressElabErrors_4173_) as usize);
                    v___f_4186_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_4186_, 0, v___x_4184_);
                    leanh::lean_closure_set(v___f_4186_, 1, v___x_4185_);
                    leanh::lean_inc(v_a_4176_);
                    v___x_4187_ = l_Lean_MessageData_hasTag(v___f_4186_, v_a_4176_);
                    if v___x_4187_ == 0 {
                        leanh::lean_dec_ref_known(v___x_4182_, 1);
                        leanh::lean_dec_ref(v___x_4180_);
                        leanh::lean_dec(v_a_4176_);
                        v___x_4188_ = leanh::lean_box(0);
                        if v_isShared_4179_ == 0 {
                            leanh::lean_ctor_set(v___x_4178_, 0, v___x_4188_);
                            v___x_4190_ = v___x_4178_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_4191_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4188_);
                            v___x_4190_ = v_reuseFailAlloc_4191_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4178_);
                        v___y_4103_ = v_a_4176_;
                        v___y_4104_ = v___y_4168_;
                        v___y_4105_ = v___y_4167_;
                        v___y_4106_ = v___x_4183_;
                        v___y_4107_ = v___x_4180_;
                        v___y_4108_ = v_fileName_4171_;
                        v___y_4109_ = v___x_4182_;
                        v___y_4110_ = v___y_4100_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_4190_;
            }
            13 => {
                v___x_4199_ = l_Lean_Syntax_getTailPos_x3f(v___y_4195_, v___y_4197_);
                leanh::lean_dec(v___y_4195_);
                if leanh::lean_obj_tag(v___x_4199_) == 0 {
                    leanh::lean_inc(v___y_4198_);
                    v___y_4166_ = v___y_4194_;
                    v___y_4167_ = v___y_4197_;
                    v___y_4168_ = v___y_4196_;
                    v___y_4169_ = v___y_4198_;
                    v___y_4170_ = v___y_4198_;
                    state = 10;
                    continue;
                } else {
                    v_val_4200_ = leanh::lean_ctor_get(v___x_4199_, 0);
                    leanh::lean_inc(v_val_4200_);
                    leanh::lean_dec_ref_known(v___x_4199_, 1);
                    v___y_4166_ = v___y_4194_;
                    v___y_4167_ = v___y_4197_;
                    v___y_4168_ = v___y_4196_;
                    v___y_4169_ = v___y_4198_;
                    v___y_4170_ = v_val_4200_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_4205_ = l_Lean_Elab_Command_getRef___redArg(v___y_4099_);
                if leanh::lean_obj_tag(v___x_4205_) == 0 {
                    v_a_4206_ = leanh::lean_ctor_get(v___x_4205_, 0);
                    leanh::lean_inc(v_a_4206_);
                    leanh::lean_dec_ref_known(v___x_4205_, 1);
                    v_ref_4207_ = l_Lean_replaceRef(v_ref_4095_, v_a_4206_);
                    leanh::lean_dec(v_a_4206_);
                    v___x_4208_ = l_Lean_Syntax_getPos_x3f(v_ref_4207_, v___y_4203_);
                    if leanh::lean_obj_tag(v___x_4208_) == 0 {
                        v___x_4209_ = leanh::lean_unsigned_to_nat(0);
                        v___y_4194_ = v___y_4202_;
                        v___y_4195_ = v_ref_4207_;
                        v___y_4196_ = v___y_4204_;
                        v___y_4197_ = v___y_4203_;
                        v___y_4198_ = v___x_4209_;
                        state = 13;
                        continue;
                    } else {
                        v_val_4210_ = leanh::lean_ctor_get(v___x_4208_, 0);
                        leanh::lean_inc(v_val_4210_);
                        leanh::lean_dec_ref_known(v___x_4208_, 1);
                        v___y_4194_ = v___y_4202_;
                        v___y_4195_ = v_ref_4207_;
                        v___y_4196_ = v___y_4204_;
                        v___y_4197_ = v___y_4203_;
                        v___y_4198_ = v_val_4210_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_4096_);
                    v_a_4211_ = leanh::lean_ctor_get(v___x_4205_, 0);
                    v_isSharedCheck_4218_ = (!leanh::lean_is_exclusive(v___x_4205_)) as u8;
                    if v_isSharedCheck_4218_ == 0 {
                        v___x_4213_ = v___x_4205_;
                        v_isShared_4214_ = v_isSharedCheck_4218_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4211_);
                        leanh::lean_dec(v___x_4205_);
                        v___x_4213_ = leanh::lean_box(0);
                        v_isShared_4214_ = v_isSharedCheck_4218_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_4214_ == 0 {
                    v___x_4216_ = v___x_4213_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4217_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
                    v___x_4216_ = v_reuseFailAlloc_4217_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4216_;
            }
            17 => {
                if v___y_4223_ == 0 {
                    v___y_4202_ = v___y_4221_;
                    v___y_4203_ = v___y_4222_;
                    v___y_4204_ = v_severity_4097_;
                    state = 14;
                    continue;
                } else {
                    v___y_4202_ = v___y_4221_;
                    v___y_4203_ = v___y_4222_;
                    v___y_4204_ = v___x_4219_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_4225_ == 0 {
                    v___x_4226_ = lean_st_ref_get(v___y_4100_);
                    v_scopes_4227_ = leanh::lean_ctor_get(v___x_4226_, 2);
                    leanh::lean_inc(v_scopes_4227_);
                    leanh::lean_dec(v___x_4226_);
                    v___x_4228_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_4229_ = l_List_head_x21___redArg(v___x_4228_, v_scopes_4227_);
                    leanh::lean_dec(v_scopes_4227_);
                    v_opts_4230_ = leanh::lean_ctor_get(v___x_4229_, 1);
                    leanh::lean_inc_ref(v_opts_4230_);
                    leanh::lean_dec(v___x_4229_);
                    v___x_4231_ = 1;
                    v___x_4232_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4097_, v___x_4231_);
                    if v___x_4232_ == 0 {
                        leanh::lean_dec_ref(v_opts_4230_);
                        v___y_4221_ = v___y_4225_;
                        v___y_4222_ = v___y_4225_;
                        v___y_4223_ = v___x_4232_;
                        state = 17;
                        continue;
                    } else {
                        v___x_4233_ = l_Lean_warningAsError;
                        v___x_4234_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_4230_, v___x_4233_);
                        leanh::lean_dec_ref(v_opts_4230_);
                        v___y_4221_ = v___y_4225_;
                        v___y_4222_ = v___y_4225_;
                        v___y_4223_ = v___x_4234_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_4096_);
                    v___x_4235_ = leanh::lean_box(0);
                    v___x_4236_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4236_, 0, v___x_4235_);
                    return v___x_4236_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(
    mut v_ref_4239_: *mut leanh::LeanObject,
    mut v_msgData_4240_: *mut leanh::LeanObject,
    mut v_severity_4241_: *mut leanh::LeanObject,
    mut v_isSilent_4242_: *mut leanh::LeanObject,
    mut v___y_4243_: *mut leanh::LeanObject,
    mut v___y_4244_: *mut leanh::LeanObject,
    mut v___y_4245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_4246_: u8 = 0;
    let mut v_isSilent_boxed_4247_: u8 = 0;
    let mut v_res_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4246_ = (leanh::lean_unbox(v_severity_4241_) as u8);
    v_isSilent_boxed_4247_ = (leanh::lean_unbox(v_isSilent_4242_) as u8);
    v_res_4248_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_4239_, v_msgData_4240_, v_severity_boxed_4246_, v_isSilent_boxed_4247_, v___y_4243_, v___y_4244_);
    leanh::lean_dec(v___y_4244_);
    leanh::lean_dec_ref(v___y_4243_);
    leanh::lean_dec(v_ref_4239_);
    return v_res_4248_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(
    mut v_msgData_4249_: *mut leanh::LeanObject,
    mut v_severity_4250_: u8,
    mut v_isSilent_4251_: u8,
    mut v___y_4252_: *mut leanh::LeanObject,
    mut v___y_4253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4261_: u8 = 0;
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4255_ = l_Lean_Elab_Command_getRef___redArg(v___y_4252_);
                if leanh::lean_obj_tag(v___x_4255_) == 0 {
                    v_a_4256_ = leanh::lean_ctor_get(v___x_4255_, 0);
                    leanh::lean_inc(v_a_4256_);
                    leanh::lean_dec_ref_known(v___x_4255_, 1);
                    v___x_4257_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_4256_, v_msgData_4249_, v_severity_4250_, v_isSilent_4251_, v___y_4252_, v___y_4253_);
                    leanh::lean_dec(v_a_4256_);
                    return v___x_4257_;
                } else {
                    leanh::lean_dec_ref(v_msgData_4249_);
                    v_a_4258_ = leanh::lean_ctor_get(v___x_4255_, 0);
                    v_isSharedCheck_4265_ = (!leanh::lean_is_exclusive(v___x_4255_)) as u8;
                    if v_isSharedCheck_4265_ == 0 {
                        v___x_4260_ = v___x_4255_;
                        v_isShared_4261_ = v_isSharedCheck_4265_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4258_);
                        leanh::lean_dec(v___x_4255_);
                        v___x_4260_ = leanh::lean_box(0);
                        v_isShared_4261_ = v_isSharedCheck_4265_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4261_ == 0 {
                    v___x_4263_ = v___x_4260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4264_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
                    v___x_4263_ = v_reuseFailAlloc_4264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(
    mut v_msgData_4266_: *mut leanh::LeanObject,
    mut v_severity_4267_: *mut leanh::LeanObject,
    mut v_isSilent_4268_: *mut leanh::LeanObject,
    mut v___y_4269_: *mut leanh::LeanObject,
    mut v___y_4270_: *mut leanh::LeanObject,
    mut v___y_4271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_4272_: u8 = 0;
    let mut v_isSilent_boxed_4273_: u8 = 0;
    let mut v_res_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4272_ = (leanh::lean_unbox(v_severity_4267_) as u8);
    v_isSilent_boxed_4273_ = (leanh::lean_unbox(v_isSilent_4268_) as u8);
    v_res_4274_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_4266_, v_severity_boxed_4272_, v_isSilent_boxed_4273_, v___y_4269_, v___y_4270_);
    leanh::lean_dec(v___y_4270_);
    leanh::lean_dec_ref(v___y_4269_);
    return v_res_4274_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(
    mut v_msgData_4275_: *mut leanh::LeanObject,
    mut v___y_4276_: *mut leanh::LeanObject,
    mut v___y_4277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4279_: u8 = 0;
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4279_ = 2;
    v___x_4280_ = 0;
    v___x_4281_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_4275_, v___x_4279_, v___x_4280_, v___y_4276_, v___y_4277_);
    return v___x_4281_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(
    mut v_msgData_4282_: *mut leanh::LeanObject,
    mut v___y_4283_: *mut leanh::LeanObject,
    mut v___y_4284_: *mut leanh::LeanObject,
    mut v___y_4285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4286_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_4282_, v___y_4283_, v___y_4284_);
    leanh::lean_dec(v___y_4284_);
    leanh::lean_dec_ref(v___y_4283_);
    return v_res_4286_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(
    mut v_ref_4287_: *mut leanh::LeanObject,
    mut v_msgData_4288_: *mut leanh::LeanObject,
    mut v___y_4289_: *mut leanh::LeanObject,
    mut v___y_4290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4292_: u8 = 0;
    let mut v___x_4293_: u8 = 0;
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4292_ = 2;
    v___x_4293_ = 0;
    v___x_4294_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_4287_, v_msgData_4288_, v___x_4292_, v___x_4293_, v___y_4289_, v___y_4290_);
    return v___x_4294_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(
    mut v_ref_4295_: *mut leanh::LeanObject,
    mut v_msgData_4296_: *mut leanh::LeanObject,
    mut v___y_4297_: *mut leanh::LeanObject,
    mut v___y_4298_: *mut leanh::LeanObject,
    mut v___y_4299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4300_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_4295_, v_msgData_4296_, v___y_4297_, v___y_4298_);
    leanh::lean_dec(v___y_4298_);
    leanh::lean_dec_ref(v___y_4297_);
    leanh::lean_dec(v_ref_4295_);
    return v_res_4300_;
}
pub unsafe fn _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4302_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0;
    v___x_4303_ = l_Lean_stringToMessageData(v___x_4302_);
    return v___x_4303_;
}
pub unsafe fn l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(
    mut v_ex_4304_: *mut leanh::LeanObject,
    mut v___y_4305_: *mut leanh::LeanObject,
    mut v___y_4306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4313_: u8 = 0;
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4323_: u8 = 0;
    let mut v_ref_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4332_: u8 = 0;
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: u8 = 0;
    let mut v___x_4336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_ex_4304_) == 0 {
                    v_ref_4308_ = leanh::lean_ctor_get(v_ex_4304_, 0);
                    leanh::lean_inc(v_ref_4308_);
                    v_msg_4309_ = leanh::lean_ctor_get(v_ex_4304_, 1);
                    leanh::lean_inc_ref(v_msg_4309_);
                    leanh::lean_dec_ref_known(v_ex_4304_, 2);
                    v___x_4310_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_4308_, v_msg_4309_, v___y_4305_, v___y_4306_);
                    leanh::lean_dec(v_ref_4308_);
                    return v___x_4310_;
                } else {
                    v_id_4311_ = leanh::lean_ctor_get(v_ex_4304_, 0);
                    leanh::lean_inc(v_id_4311_);
                    v___x_4335_ = l_Lean_Elab_isAbortExceptionId(v_id_4311_);
                    if v___x_4335_ == 0 {
                        v___x_4336_ = l_Lean_Exception_isInterrupt(v_ex_4304_);
                        leanh::lean_dec_ref_known(v_ex_4304_, 2);
                        v___y_4313_ = v___x_4336_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v_ex_4304_, 2);
                        v___y_4313_ = v___x_4335_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_4313_ == 0 {
                    v___x_4314_ = l_Lean_InternalExceptionId_getName(v_id_4311_);
                    leanh::lean_dec(v_id_4311_);
                    if leanh::lean_obj_tag(v___x_4314_) == 0 {
                        v_a_4315_ = leanh::lean_ctor_get(v___x_4314_, 0);
                        leanh::lean_inc(v_a_4315_);
                        leanh::lean_dec_ref_known(v___x_4314_, 1);
                        v___x_4316_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once), _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
                        v___x_4317_ = l_Lean_MessageData_ofName(v_a_4315_);
                        v___x_4318_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4318_, 0, v___x_4316_);
                        leanh::lean_ctor_set(v___x_4318_, 1, v___x_4317_);
                        v___x_4319_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_4318_, v___y_4305_, v___y_4306_);
                        return v___x_4319_;
                    } else {
                        v_a_4320_ = leanh::lean_ctor_get(v___x_4314_, 0);
                        v_isSharedCheck_4332_ =
                            (!leanh::lean_is_exclusive(v___x_4314_)) as u8;
                        if v_isSharedCheck_4332_ == 0 {
                            v___x_4322_ = v___x_4314_;
                            v_isShared_4323_ = v_isSharedCheck_4332_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4320_);
                            leanh::lean_dec(v___x_4314_);
                            v___x_4322_ = leanh::lean_box(0);
                            v_isShared_4323_ = v_isSharedCheck_4332_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_id_4311_);
                    v___x_4333_ = leanh::lean_box(0);
                    v___x_4334_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4334_, 0, v___x_4333_);
                    return v___x_4334_;
                }
            }
            2 => {
                v_ref_4324_ = leanh::lean_ctor_get(v___y_4305_, 7);
                v___x_4325_ = lean_io_error_to_string(v_a_4320_);
                v___x_4326_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4326_, 0, v___x_4325_);
                v___x_4327_ = l_Lean_MessageData_ofFormat(v___x_4326_);
                leanh::lean_inc(v_ref_4324_);
                v___x_4328_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4328_, 0, v_ref_4324_);
                leanh::lean_ctor_set(v___x_4328_, 1, v___x_4327_);
                if v_isShared_4323_ == 0 {
                    leanh::lean_ctor_set(v___x_4322_, 0, v___x_4328_);
                    v___x_4330_ = v___x_4322_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4331_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4328_);
                    v___x_4330_ = v_reuseFailAlloc_4331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(
    mut v_ex_4337_: *mut leanh::LeanObject,
    mut v___y_4338_: *mut leanh::LeanObject,
    mut v___y_4339_: *mut leanh::LeanObject,
    mut v___y_4340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4341_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_4337_, v___y_4338_, v___y_4339_);
    leanh::lean_dec(v___y_4339_);
    leanh::lean_dec_ref(v___y_4338_);
    return v_res_4341_;
}
pub unsafe fn l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(
    mut v_x_4342_: *mut leanh::LeanObject,
    mut v___y_4343_: *mut leanh::LeanObject,
    mut v___y_4344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4344_);
    leanh::lean_inc_ref(v___y_4343_);
    v___x_4346_ = leanh::lean_apply_3(
        v_x_4342_,
        v___y_4343_,
        v___y_4344_,
        leanh::lean_box(0),
    );
    if leanh::lean_obj_tag(v___x_4346_) == 0 {
        return v___x_4346_;
    } else {
        let mut v_a_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4348_: u8 = 0;
        v_a_4347_ = leanh::lean_ctor_get(v___x_4346_, 0);
        leanh::lean_inc(v_a_4347_);
        v___x_4348_ = l_Lean_Exception_isInterrupt(v_a_4347_);
        if v___x_4348_ == 0 {
            let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_4346_, 1);
            v___x_4349_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_4347_, v___y_4343_, v___y_4344_);
            return v___x_4349_;
        } else {
            leanh::lean_dec(v_a_4347_);
            return v___x_4346_;
        }
    }
}
pub unsafe fn l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(
    mut v_x_4350_: *mut leanh::LeanObject,
    mut v___y_4351_: *mut leanh::LeanObject,
    mut v___y_4352_: *mut leanh::LeanObject,
    mut v___y_4353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4354_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_4350_, v___y_4351_, v___y_4352_);
    leanh::lean_dec(v___y_4352_);
    leanh::lean_dec_ref(v___y_4351_);
    return v_res_4354_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(
    mut v___f_4355_: *mut leanh::LeanObject,
    mut v___x_4356_: *mut leanh::LeanObject,
    mut v_val_4357_: *mut leanh::LeanObject,
    mut v___y_4358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4368_: u8 = 0;
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4372_: u8 = 0;
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4363_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_4355_, v___x_4356_, v_val_4357_);
                if leanh::lean_obj_tag(v___x_4363_) == 0 {
                    if leanh::lean_obj_tag(v___x_4363_) == 0 {
                        v_a_4364_ = leanh::lean_ctor_get(v___x_4363_, 0);
                        leanh::lean_inc(v_a_4364_);
                        leanh::lean_dec_ref_known(v___x_4363_, 1);
                        v_a_4361_ = v_a_4364_;
                        state = 1;
                        continue;
                    } else {
                        v_a_4365_ = leanh::lean_ctor_get(v___x_4363_, 0);
                        v_isSharedCheck_4372_ =
                            (!leanh::lean_is_exclusive(v___x_4363_)) as u8;
                        if v_isSharedCheck_4372_ == 0 {
                            v___x_4367_ = v___x_4363_;
                            v_isShared_4368_ = v_isSharedCheck_4372_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4365_);
                            leanh::lean_dec(v___x_4363_);
                            v___x_4367_ = leanh::lean_box(0);
                            v_isShared_4368_ = v_isSharedCheck_4372_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_4363_, 1);
                    v___x_4373_ = leanh::lean_box(0);
                    v_a_4361_ = v___x_4373_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4362_, 0, v_a_4361_);
                return v___x_4362_;
            }
            2 => {
                if v_isShared_4368_ == 0 {
                    v___x_4370_ = v___x_4367_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4371_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
                    v___x_4370_ = v_reuseFailAlloc_4371_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(
    mut v___f_4374_: *mut leanh::LeanObject,
    mut v___x_4375_: *mut leanh::LeanObject,
    mut v_val_4376_: *mut leanh::LeanObject,
    mut v___y_4377_: *mut leanh::LeanObject,
    mut v___y_4378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4379_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(
        v___f_4374_,
        v___x_4375_,
        v_val_4376_,
        v___y_4377_,
    );
    leanh::lean_dec_ref(v___y_4377_);
    leanh::lean_dec(v_val_4376_);
    leanh::lean_dec_ref(v___x_4375_);
    return v_res_4379_;
}
pub unsafe fn l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(
    mut v_h_4380_: *mut leanh::LeanObject,
    mut v_x_4381_: *mut leanh::LeanObject,
    mut v___y_4382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4384_ = lean_get_set_stderr(v_h_4380_);
    leanh::lean_inc_ref(v___y_4382_);
    v___x_4385_ = leanh::lean_apply_2(v_x_4381_, v___y_4382_, leanh::lean_box(0));
    v___x_4386_ = lean_get_set_stderr(v___x_4384_);
    leanh::lean_dec_ref(v___x_4386_);
    return v___x_4385_;
}
pub unsafe fn l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(
    mut v_h_4387_: *mut leanh::LeanObject,
    mut v_x_4388_: *mut leanh::LeanObject,
    mut v___y_4389_: *mut leanh::LeanObject,
    mut v___y_4390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4391_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_4387_, v_x_4388_, v___y_4389_);
    leanh::lean_dec_ref(v___y_4389_);
    return v_res_4391_;
}
pub unsafe fn l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(
    mut v_00_u03b1_4392_: *mut leanh::LeanObject,
    mut v_h_4393_: *mut leanh::LeanObject,
    mut v_x_4394_: *mut leanh::LeanObject,
    mut v___y_4395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4397_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_4393_, v_x_4394_, v___y_4395_);
    return v___x_4397_;
}
pub unsafe fn l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(
    mut v_00_u03b1_4398_: *mut leanh::LeanObject,
    mut v_h_4399_: *mut leanh::LeanObject,
    mut v_x_4400_: *mut leanh::LeanObject,
    mut v___y_4401_: *mut leanh::LeanObject,
    mut v___y_4402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4403_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_4398_, v_h_4399_, v_x_4400_, v___y_4401_);
    leanh::lean_dec_ref(v___y_4401_);
    return v_res_4403_;
}
pub unsafe fn l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(
    mut v_h_4404_: *mut leanh::LeanObject,
    mut v_x_4405_: *mut leanh::LeanObject,
    mut v___y_4406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4408_ = lean_get_set_stdin(v_h_4404_);
    leanh::lean_inc_ref(v___y_4406_);
    v___x_4409_ = leanh::lean_apply_2(v_x_4405_, v___y_4406_, leanh::lean_box(0));
    v___x_4410_ = lean_get_set_stdin(v___x_4408_);
    leanh::lean_dec_ref(v___x_4410_);
    return v___x_4409_;
}
pub unsafe fn l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(
    mut v_h_4411_: *mut leanh::LeanObject,
    mut v_x_4412_: *mut leanh::LeanObject,
    mut v___y_4413_: *mut leanh::LeanObject,
    mut v___y_4414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4415_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_4411_, v_x_4412_, v___y_4413_);
    leanh::lean_dec_ref(v___y_4413_);
    return v_res_4415_;
}
pub unsafe fn l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(
    mut v_msg_4416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4417_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0;
    v___x_4418_ = lean_panic_fn_borrowed(v___x_4417_, v_msg_4416_);
    return v___x_4418_;
}
pub unsafe fn l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(
    mut v_h_4419_: *mut leanh::LeanObject,
    mut v_x_4420_: *mut leanh::LeanObject,
    mut v___y_4421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4423_ = lean_get_set_stdout(v_h_4419_);
    leanh::lean_inc_ref(v___y_4421_);
    v___x_4424_ = leanh::lean_apply_2(v_x_4420_, v___y_4421_, leanh::lean_box(0));
    v___x_4425_ = lean_get_set_stdout(v___x_4423_);
    leanh::lean_dec_ref(v___x_4425_);
    return v___x_4424_;
}
pub unsafe fn l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(
    mut v_h_4426_: *mut leanh::LeanObject,
    mut v_x_4427_: *mut leanh::LeanObject,
    mut v___y_4428_: *mut leanh::LeanObject,
    mut v___y_4429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4430_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_4426_, v_x_4427_, v___y_4428_);
    leanh::lean_dec_ref(v___y_4428_);
    return v_res_4430_;
}
pub unsafe fn l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(
    mut v_00_u03b1_4431_: *mut leanh::LeanObject,
    mut v_h_4432_: *mut leanh::LeanObject,
    mut v_x_4433_: *mut leanh::LeanObject,
    mut v___y_4434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4436_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_4432_, v_x_4433_, v___y_4434_);
    return v___x_4436_;
}
pub unsafe fn l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(
    mut v_00_u03b1_4437_: *mut leanh::LeanObject,
    mut v_h_4438_: *mut leanh::LeanObject,
    mut v_x_4439_: *mut leanh::LeanObject,
    mut v___y_4440_: *mut leanh::LeanObject,
    mut v___y_4441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4442_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_4437_, v_h_4438_, v_x_4439_, v___y_4440_);
    leanh::lean_dec_ref(v___y_4440_);
    return v_res_4442_;
}
pub unsafe fn _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4443_ = leanh::lean_unsigned_to_nat(0);
    v___x_4444_ = l_ByteArray_empty;
    v___x_4445_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4445_, 0, v___x_4444_);
    leanh::lean_ctor_set(v___x_4445_, 1, v___x_4443_);
    return v___x_4445_;
}
pub unsafe fn _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4449_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3;
    v___x_4450_ = leanh::lean_unsigned_to_nat(46);
    v___x_4451_ = leanh::lean_unsigned_to_nat(193);
    v___x_4452_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2;
    v___x_4453_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1;
    v___x_4454_ = l_mkPanicMessageWithDecl(
        v___x_4453_,
        v___x_4452_,
        v___x_4451_,
        v___x_4450_,
        v___x_4449_,
    );
    return v___x_4454_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(
    mut v_x_4455_: *mut leanh::LeanObject,
    mut v_isolateStderr_4456_: u8,
    mut v___y_4457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: u8 = 0;
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4463_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once), _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
                v___x_4464_ = lean_st_mk_ref(v___x_4463_);
                v___x_4465_ = lean_st_mk_ref(v___x_4463_);
                v___x_4466_ = l_IO_FS_Stream_ofBuffer(v___x_4464_);
                leanh::lean_inc(v___x_4465_);
                v___x_4467_ = l_IO_FS_Stream_ofBuffer(v___x_4465_);
                if v_isolateStderr_4456_ == 0 {
                    v___y_4469_ = v_x_4455_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc_ref(v___x_4467_);
                    v___x_4478_ = leanh::lean_alloc_closure(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed as *mut core::ffi::c_void, 5, 3);
                    leanh::lean_closure_set(v___x_4478_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_4478_, 1, v___x_4467_);
                    leanh::lean_closure_set(v___x_4478_, 2, v_x_4455_);
                    v___y_4469_ = v___x_4478_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4462_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4462_, 0, v___y_4461_);
                leanh::lean_ctor_set(v___x_4462_, 1, v___y_4460_);
                return v___x_4462_;
            }
            2 => {
                v___x_4470_ = leanh::lean_alloc_closure(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed as *mut core::ffi::c_void, 5, 3);
                leanh::lean_closure_set(v___x_4470_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_4470_, 1, v___x_4467_);
                leanh::lean_closure_set(v___x_4470_, 2, v___y_4469_);
                v___x_4471_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_4466_, v___x_4470_, v___y_4457_);
                v___x_4472_ = lean_st_ref_get(v___x_4465_);
                leanh::lean_dec(v___x_4465_);
                v_data_4473_ = leanh::lean_ctor_get(v___x_4472_, 0);
                leanh::lean_inc_ref(v_data_4473_);
                leanh::lean_dec(v___x_4472_);
                v___x_4474_ = lean_string_validate_utf8(v_data_4473_);
                if v___x_4474_ == 0 {
                    leanh::lean_dec_ref(v_data_4473_);
                    v___x_4475_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once), _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
                    v___x_4476_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_4475_);
                    v___y_4460_ = v___x_4471_;
                    v___y_4461_ = v___x_4476_;
                    state = 1;
                    continue;
                } else {
                    v___x_4477_ = lean_string_from_utf8_unchecked(v_data_4473_);
                    v___y_4460_ = v___x_4471_;
                    v___y_4461_ = v___x_4477_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(
    mut v_x_4479_: *mut leanh::LeanObject,
    mut v_isolateStderr_4480_: *mut leanh::LeanObject,
    mut v___y_4481_: *mut leanh::LeanObject,
    mut v___y_4482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isolateStderr_boxed_4483_: u8 = 0;
    let mut v_res_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isolateStderr_boxed_4483_ = (leanh::lean_unbox(v_isolateStderr_4480_) as u8);
    v_res_4484_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_4479_, v_isolateStderr_boxed_4483_, v___y_4481_);
    leanh::lean_dec_ref(v___y_4481_);
    return v_res_4484_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4493_: u8 = 0;
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4493_ = 1;
    v___x_4494_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3;
    v___x_4495_ = l_Lean_Name_toString(v___x_4494_, v___x_4493_);
    return v___x_4495_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(
    mut v_stx_4496_: *mut leanh::LeanObject,
    mut v_cmdState_4497_: *mut leanh::LeanObject,
    mut v_beginPos_4498_: *mut leanh::LeanObject,
    mut v_snap_4499_: *mut leanh::LeanObject,
    mut v_cancelTk_4500_: *mut leanh::LeanObject,
    mut v_a_4501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_env_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4513_: u8 = 0;
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcessingContext_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: u8 = 0;
    let mut v___y_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4537_: u8 = 0;
    let mut v_messages_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_new_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4557_: u8 = 0;
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4561_: u8 = 0;
    let mut v_unused_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: u8 = 0;
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: u8 = 0;
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: u8 = 0;
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4586_: u8 = 0;
    let mut v_unused_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_env_4503_ = leanh::lean_ctor_get(v_cmdState_4497_, 0);
                v_scopes_4504_ = leanh::lean_ctor_get(v_cmdState_4497_, 2);
                v_usedQuotCtxts_4505_ = leanh::lean_ctor_get(v_cmdState_4497_, 3);
                v_nextMacroScope_4506_ = leanh::lean_ctor_get(v_cmdState_4497_, 4);
                v_maxRecDepth_4507_ = leanh::lean_ctor_get(v_cmdState_4497_, 5);
                v_ngen_4508_ = leanh::lean_ctor_get(v_cmdState_4497_, 6);
                v_auxDeclNGen_4509_ = leanh::lean_ctor_get(v_cmdState_4497_, 7);
                v_infoState_4510_ = leanh::lean_ctor_get(v_cmdState_4497_, 8);
                v_isSharedCheck_4586_ = (!leanh::lean_is_exclusive(v_cmdState_4497_)) as u8;
                if v_isSharedCheck_4586_ == 0 {
                    v_unused_4587_ = leanh::lean_ctor_get(v_cmdState_4497_, 10);
                    leanh::lean_dec(v_unused_4587_);
                    v_unused_4588_ = leanh::lean_ctor_get(v_cmdState_4497_, 9);
                    leanh::lean_dec(v_unused_4588_);
                    v_unused_4589_ = leanh::lean_ctor_get(v_cmdState_4497_, 1);
                    leanh::lean_dec(v_unused_4589_);
                    v___x_4512_ = v_cmdState_4497_;
                    v_isShared_4513_ = v_isSharedCheck_4586_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_infoState_4510_);
                    leanh::lean_inc(v_auxDeclNGen_4509_);
                    leanh::lean_inc(v_ngen_4508_);
                    leanh::lean_inc(v_maxRecDepth_4507_);
                    leanh::lean_inc(v_nextMacroScope_4506_);
                    leanh::lean_inc(v_usedQuotCtxts_4505_);
                    leanh::lean_inc(v_scopes_4504_);
                    leanh::lean_inc(v_env_4503_);
                    leanh::lean_dec(v_cmdState_4497_);
                    v___x_4512_ = leanh::lean_box(0);
                    v_isShared_4513_ = v_isSharedCheck_4586_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4514_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_4515_ = l_List_head_x21___redArg(v___x_4514_, v_scopes_4504_);
                v___x_4516_ = l_Lean_MessageLog_empty;
                v___x_4517_ = leanh::lean_unsigned_to_nat(0);
                v___x_4518_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
                v___x_4519_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0;
                if v_isShared_4513_ == 0 {
                    leanh::lean_ctor_set(v___x_4512_, 10, v___x_4519_);
                    leanh::lean_ctor_set(v___x_4512_, 9, v___x_4518_);
                    leanh::lean_ctor_set(v___x_4512_, 1, v___x_4516_);
                    v___x_4521_ = v___x_4512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4585_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_env_4503_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 1, v___x_4516_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 2, v_scopes_4504_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 3, v_usedQuotCtxts_4505_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 4, v_nextMacroScope_4506_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 5, v_maxRecDepth_4507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 6, v_ngen_4508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 7, v_auxDeclNGen_4509_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 8, v_infoState_4510_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 9, v___x_4518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 10, v___x_4519_);
                    v___x_4521_ = v_reuseFailAlloc_4585_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4522_ = lean_st_mk_ref(v___x_4521_);
                v_toProcessingContext_4523_ = leanh::lean_ctor_get(v_a_4501_, 0);
                v_fileName_4524_ = leanh::lean_ctor_get(v_toProcessingContext_4523_, 1);
                v_fileMap_4525_ = leanh::lean_ctor_get(v_toProcessingContext_4523_, 2);
                v_opts_4526_ = leanh::lean_ctor_get(v___x_4515_, 1);
                leanh::lean_inc_ref(v_opts_4526_);
                leanh::lean_dec(v___x_4515_);
                v___f_4527_ = leanh::lean_alloc_closure(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                leanh::lean_closure_set(v___f_4527_, 0, v_stx_4496_);
                v___x_4528_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
                v___x_4529_ = leanh::lean_box(0);
                v___x_4530_ = leanh::lean_box(0);
                v___x_4531_ = l_Lean_firstFrontendMacroScope;
                v___x_4532_ = leanh::lean_box(0);
                v___x_4533_ = l_Lean_internal_cmdlineSnapshots;
                v___x_4534_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_4526_, v___x_4533_);
                if v___x_4534_ == 0 {
                    leanh::lean_inc_ref(v_snap_4499_);
                    v___x_4584_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4584_, 0, v_snap_4499_);
                    v___y_4564_ = v___x_4584_;
                    state = 6;
                    continue;
                } else {
                    v___y_4564_ = v___x_4530_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                v_new_4539_ = leanh::lean_ctor_get(v_snap_4499_, 1);
                leanh::lean_inc(v_new_4539_);
                leanh::lean_dec_ref(v_snap_4499_);
                v___x_4540_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
                v___x_4541_ = l_Lean_Language_Snapshot_Diagnostics_empty;
                v___x_4542_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_4542_, 0, v___x_4540_);
                leanh::lean_ctor_set(v___x_4542_, 1, v___x_4541_);
                leanh::lean_ctor_set(v___x_4542_, 2, v___x_4530_);
                leanh::lean_ctor_set(v___x_4542_, 3, v___x_4518_);
                leanh::lean_ctor_set_uint8(
                    v___x_4542_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___y_4537_,
                );
                v___x_4543_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_4528_, v___x_4542_);
                v___x_4544_ = lean_io_promise_resolve(v___x_4543_, v_new_4539_);
                leanh::lean_dec(v_new_4539_);
                v_env_4545_ = leanh::lean_ctor_get(v___y_4536_, 0);
                v_scopes_4546_ = leanh::lean_ctor_get(v___y_4536_, 2);
                v_usedQuotCtxts_4547_ = leanh::lean_ctor_get(v___y_4536_, 3);
                v_nextMacroScope_4548_ = leanh::lean_ctor_get(v___y_4536_, 4);
                v_maxRecDepth_4549_ = leanh::lean_ctor_get(v___y_4536_, 5);
                v_ngen_4550_ = leanh::lean_ctor_get(v___y_4536_, 6);
                v_auxDeclNGen_4551_ = leanh::lean_ctor_get(v___y_4536_, 7);
                v_infoState_4552_ = leanh::lean_ctor_get(v___y_4536_, 8);
                v_traceState_4553_ = leanh::lean_ctor_get(v___y_4536_, 9);
                v_snapshotTasks_4554_ = leanh::lean_ctor_get(v___y_4536_, 10);
                v_isSharedCheck_4561_ = (!leanh::lean_is_exclusive(v___y_4536_)) as u8;
                if v_isSharedCheck_4561_ == 0 {
                    v_unused_4562_ = leanh::lean_ctor_get(v___y_4536_, 1);
                    leanh::lean_dec(v_unused_4562_);
                    v___x_4556_ = v___y_4536_;
                    v_isShared_4557_ = v_isSharedCheck_4561_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4554_);
                    leanh::lean_inc(v_traceState_4553_);
                    leanh::lean_inc(v_infoState_4552_);
                    leanh::lean_inc(v_auxDeclNGen_4551_);
                    leanh::lean_inc(v_ngen_4550_);
                    leanh::lean_inc(v_maxRecDepth_4549_);
                    leanh::lean_inc(v_nextMacroScope_4548_);
                    leanh::lean_inc(v_usedQuotCtxts_4547_);
                    leanh::lean_inc(v_scopes_4546_);
                    leanh::lean_inc(v_env_4545_);
                    leanh::lean_dec(v___y_4536_);
                    v___x_4556_ = leanh::lean_box(0);
                    v_isShared_4557_ = v_isSharedCheck_4561_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4557_ == 0 {
                    leanh::lean_ctor_set(v___x_4556_, 1, v_messages_4538_);
                    v___x_4559_ = v___x_4556_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4560_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_env_4545_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 1, v_messages_4538_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 2, v_scopes_4546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 3, v_usedQuotCtxts_4547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 4, v_nextMacroScope_4548_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 5, v_maxRecDepth_4549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 6, v_ngen_4550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 7, v_auxDeclNGen_4551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 8, v_infoState_4552_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 9, v_traceState_4553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 10, v_snapshotTasks_4554_);
                    v___x_4559_ = v_reuseFailAlloc_4560_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4559_;
            }
            6 => {
                v___x_4565_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4565_, 0, v_cancelTk_4500_);
                v___x_4566_ = 0;
                leanh::lean_inc(v_beginPos_4498_);
                leanh::lean_inc_ref(v_fileMap_4525_);
                leanh::lean_inc_ref(v_fileName_4524_);
                v___x_4567_ = leanh::lean_alloc_ctor(0, 10, (1) as u32);
                leanh::lean_ctor_set(v___x_4567_, 0, v_fileName_4524_);
                leanh::lean_ctor_set(v___x_4567_, 1, v_fileMap_4525_);
                leanh::lean_ctor_set(v___x_4567_, 2, v___x_4517_);
                leanh::lean_ctor_set(v___x_4567_, 3, v_beginPos_4498_);
                leanh::lean_ctor_set(v___x_4567_, 4, v___x_4529_);
                leanh::lean_ctor_set(v___x_4567_, 5, v___x_4530_);
                leanh::lean_ctor_set(v___x_4567_, 6, v___x_4531_);
                leanh::lean_ctor_set(v___x_4567_, 7, v___x_4532_);
                leanh::lean_ctor_set(v___x_4567_, 8, v___y_4564_);
                leanh::lean_ctor_set(v___x_4567_, 9, v___x_4565_);
                leanh::lean_ctor_set_uint8(
                    v___x_4567_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                    v___x_4566_,
                );
                leanh::lean_inc(v___x_4522_);
                v___f_4568_ = leanh::lean_alloc_closure(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed as *mut core::ffi::c_void, 5, 3);
                leanh::lean_closure_set(v___f_4568_, 0, v___f_4527_);
                leanh::lean_closure_set(v___f_4568_, 1, v___x_4567_);
                leanh::lean_closure_set(v___f_4568_, 2, v___x_4522_);
                v___x_4569_ = l_Lean_Core_stderrAsMessages;
                v___x_4570_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_4526_, v___x_4569_);
                leanh::lean_dec_ref(v_opts_4526_);
                v___x_4571_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_4568_, v___x_4570_, v_a_4501_);
                v_fst_4572_ = leanh::lean_ctor_get(v___x_4571_, 0);
                leanh::lean_inc(v_fst_4572_);
                leanh::lean_dec_ref(v___x_4571_);
                v___x_4573_ = lean_st_ref_get(v___x_4522_);
                leanh::lean_dec(v___x_4522_);
                v_messages_4574_ = leanh::lean_ctor_get(v___x_4573_, 1);
                leanh::lean_inc_ref(v_messages_4574_);
                v___x_4575_ = lean_string_utf8_byte_size(v_fst_4572_);
                v___x_4576_ = lean_nat_dec_eq(v___x_4575_, v___x_4517_);
                if v___x_4576_ == 0 {
                    leanh::lean_inc_ref(v_fileMap_4525_);
                    v___x_4577_ = l_Lean_FileMap_toPosition(v_fileMap_4525_, v_beginPos_4498_);
                    leanh::lean_dec(v_beginPos_4498_);
                    v___x_4578_ = 0;
                    v___x_4579_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0;
                    v___x_4580_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4580_, 0, v_fst_4572_);
                    v___x_4581_ = l_Lean_MessageData_ofFormat(v___x_4580_);
                    leanh::lean_inc_ref(v_fileName_4524_);
                    v___x_4582_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                    leanh::lean_ctor_set(v___x_4582_, 0, v_fileName_4524_);
                    leanh::lean_ctor_set(v___x_4582_, 1, v___x_4577_);
                    leanh::lean_ctor_set(v___x_4582_, 2, v___x_4530_);
                    leanh::lean_ctor_set(v___x_4582_, 3, v___x_4579_);
                    leanh::lean_ctor_set(v___x_4582_, 4, v___x_4581_);
                    leanh::lean_ctor_set_uint8(
                        v___x_4582_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        v___x_4566_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_4582_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                        v___x_4578_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_4582_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                        v___x_4566_,
                    );
                    v___x_4583_ = l_Lean_MessageLog_add(v___x_4582_, v_messages_4574_);
                    v___y_4536_ = v___x_4573_;
                    v___y_4537_ = v___x_4566_;
                    v_messages_4538_ = v___x_4583_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_4572_);
                    leanh::lean_dec(v_beginPos_4498_);
                    v___y_4536_ = v___x_4573_;
                    v___y_4537_ = v___x_4566_;
                    v_messages_4538_ = v_messages_4574_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(
    mut v_stx_4590_: *mut leanh::LeanObject,
    mut v_cmdState_4591_: *mut leanh::LeanObject,
    mut v_beginPos_4592_: *mut leanh::LeanObject,
    mut v_snap_4593_: *mut leanh::LeanObject,
    mut v_cancelTk_4594_: *mut leanh::LeanObject,
    mut v_a_4595_: *mut leanh::LeanObject,
    mut v_a_4596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4597_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(
        v_stx_4590_,
        v_cmdState_4591_,
        v_beginPos_4592_,
        v_snap_4593_,
        v_cancelTk_4594_,
        v_a_4595_,
    );
    leanh::lean_dec_ref(v_a_4595_);
    return v_res_4597_;
}
pub unsafe fn l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(
    mut v_00_u03b1_4598_: *mut leanh::LeanObject,
    mut v_h_4599_: *mut leanh::LeanObject,
    mut v_x_4600_: *mut leanh::LeanObject,
    mut v___y_4601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4603_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_4599_, v_x_4600_, v___y_4601_);
    return v___x_4603_;
}
pub unsafe fn l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(
    mut v_00_u03b1_4604_: *mut leanh::LeanObject,
    mut v_h_4605_: *mut leanh::LeanObject,
    mut v_x_4606_: *mut leanh::LeanObject,
    mut v___y_4607_: *mut leanh::LeanObject,
    mut v___y_4608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4609_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_4604_, v_h_4605_, v_x_4606_, v___y_4607_);
    leanh::lean_dec_ref(v___y_4607_);
    return v_res_4609_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(
    mut v_00_u03b1_4610_: *mut leanh::LeanObject,
    mut v_x_4611_: *mut leanh::LeanObject,
    mut v_isolateStderr_4612_: u8,
    mut v___y_4613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4615_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_4611_, v_isolateStderr_4612_, v___y_4613_);
    return v___x_4615_;
}
pub unsafe fn l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(
    mut v_00_u03b1_4616_: *mut leanh::LeanObject,
    mut v_x_4617_: *mut leanh::LeanObject,
    mut v_isolateStderr_4618_: *mut leanh::LeanObject,
    mut v___y_4619_: *mut leanh::LeanObject,
    mut v___y_4620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isolateStderr_boxed_4621_: u8 = 0;
    let mut v_res_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isolateStderr_boxed_4621_ = (leanh::lean_unbox(v_isolateStderr_4618_) as u8);
    v_res_4622_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_4616_, v_x_4617_, v_isolateStderr_boxed_4621_, v___y_4619_);
    leanh::lean_dec_ref(v___y_4619_);
    return v_res_4622_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(
    mut v_msgData_4623_: *mut leanh::LeanObject,
    mut v___y_4624_: *mut leanh::LeanObject,
    mut v___y_4625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4627_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_4623_, v___y_4625_);
    return v___x_4627_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(
    mut v_msgData_4628_: *mut leanh::LeanObject,
    mut v___y_4629_: *mut leanh::LeanObject,
    mut v___y_4630_: *mut leanh::LeanObject,
    mut v___y_4631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4632_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_4628_, v___y_4629_, v___y_4630_);
    leanh::lean_dec(v___y_4630_);
    leanh::lean_dec_ref(v___y_4629_);
    return v_res_4632_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(
    mut v_opts_4633_: *mut leanh::LeanObject,
    mut v_opt_4634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4635_ = leanh::lean_ctor_get(v_opt_4634_, 0);
    v_defValue_4636_ = leanh::lean_ctor_get(v_opt_4634_, 1);
    v_map_4637_ = leanh::lean_ctor_get(v_opts_4633_, 0);
    v___x_4638_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4637_,
            v_name_4635_,
        );
    if leanh::lean_obj_tag(v___x_4638_) == 0 {
        leanh::lean_inc(v_defValue_4636_);
        return v_defValue_4636_;
    } else {
        let mut v_val_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4639_ = leanh::lean_ctor_get(v___x_4638_, 0);
        leanh::lean_inc(v_val_4639_);
        leanh::lean_dec_ref_known(v___x_4638_, 1);
        if leanh::lean_obj_tag(v_val_4639_) == 3 {
            let mut v_v_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_4640_ = leanh::lean_ctor_get(v_val_4639_, 0);
            leanh::lean_inc(v_v_4640_);
            leanh::lean_dec_ref_known(v_val_4639_, 1);
            return v_v_4640_;
        } else {
            leanh::lean_dec(v_val_4639_);
            leanh::lean_inc(v_defValue_4636_);
            return v_defValue_4636_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0___boxed(
    mut v_opts_4641_: *mut leanh::LeanObject,
    mut v_opt_4642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4643_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(v_opts_4641_, v_opt_4642_);
    leanh::lean_dec_ref(v_opt_4642_);
    leanh::lean_dec_ref(v_opts_4641_);
    return v_res_4643_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(
    mut v_s_4644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4645_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0;
    v___x_4646_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4646_, 0, v_s_4644_);
    leanh::lean_ctor_set(v___x_4646_, 1, v___x_4645_);
    return v___x_4646_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(
    mut v_s_4647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSnapshot_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4651_: u8 = 0;
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4656_: u8 = 0;
    let mut v_unused_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_4648_ = leanh::lean_ctor_get(v_s_4647_, 0);
                v_isSharedCheck_4656_ = (!leanh::lean_is_exclusive(v_s_4647_)) as u8;
                if v_isSharedCheck_4656_ == 0 {
                    v_unused_4657_ = leanh::lean_ctor_get(v_s_4647_, 1);
                    leanh::lean_dec(v_unused_4657_);
                    v___x_4650_ = v_s_4647_;
                    v_isShared_4651_ = v_isSharedCheck_4656_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toSnapshot_4648_);
                    leanh::lean_dec(v_s_4647_);
                    v___x_4650_ = leanh::lean_box(0);
                    v_isShared_4651_ = v_isSharedCheck_4656_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4652_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0;
                if v_isShared_4651_ == 0 {
                    leanh::lean_ctor_set(v___x_4650_, 1, v___x_4652_);
                    v___x_4654_ = v___x_4650_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4655_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_toSnapshot_4648_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 1, v___x_4652_);
                    v___x_4654_ = v_reuseFailAlloc_4655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(
    mut v_s_4658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tree_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tree_4659_ = leanh::lean_ctor_get(v_s_4658_, 1);
    v___x_4660_ = lean_thunk_get_own(v_tree_4659_);
    return v___x_4660_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(
    mut v_s_4661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4662_ =
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_s_4661_);
    leanh::lean_dec_ref(v_s_4661_);
    return v_res_4662_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(
    mut v_a_4663_: *mut leanh::LeanObject,
    mut v___x_4664_: *mut leanh::LeanObject,
    mut v_parserState_4665_: *mut leanh::LeanObject,
    mut v_x_4666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toProcessingContext_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toProcessingContext_4667_ = leanh::lean_ctor_get(v_a_4663_, 0);
    v___x_4668_ = l_Lean_MessageLog_empty;
    leanh::lean_inc_ref(v_toProcessingContext_4667_);
    v___x_4669_ = l_Lean_Parser_parseCommand(
        v_toProcessingContext_4667_,
        v___x_4664_,
        v_parserState_4665_,
        v___x_4668_,
    );
    return v___x_4669_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(
    mut v_a_4670_: *mut leanh::LeanObject,
    mut v___x_4671_: *mut leanh::LeanObject,
    mut v_parserState_4672_: *mut leanh::LeanObject,
    mut v_x_4673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4674_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(
        v_a_4670_,
        v___x_4671_,
        v_parserState_4672_,
        v_x_4673_,
    );
    leanh::lean_dec_ref(v_a_4670_);
    return v_res_4674_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(
    mut v___x_4675_: *mut leanh::LeanObject,
    mut v___x_4676_: *mut leanh::LeanObject,
    mut v___x_4677_: *mut leanh::LeanObject,
    mut v_val_4678_: u8,
    mut v_as_4679_: *mut leanh::LeanObject,
    mut v_sz_4680_: usize,
    mut v_i_4681_: usize,
    mut v_b_4682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4684_: u8 = 0;
    let mut v_snd_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4688_: u8 = 0;
    let mut v_a_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: u8 = 0;
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: usize = 0;
    let mut v___x_4700_: usize = 0;
    let mut v_reuseFailAlloc_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4703_: u8 = 0;
    let mut v_unused_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4684_ = lean_usize_dec_lt(v_i_4681_, v_sz_4680_);
                if v___x_4684_ == 0 {
                    leanh::lean_dec_ref(v___x_4677_);
                    leanh::lean_dec_ref(v___x_4675_);
                    return v_b_4682_;
                } else {
                    v_snd_4685_ = leanh::lean_ctor_get(v_b_4682_, 1);
                    v_isSharedCheck_4703_ = (!leanh::lean_is_exclusive(v_b_4682_)) as u8;
                    if v_isSharedCheck_4703_ == 0 {
                        v_unused_4704_ = leanh::lean_ctor_get(v_b_4682_, 0);
                        leanh::lean_dec(v_unused_4704_);
                        v___x_4687_ = v_b_4682_;
                        v_isShared_4688_ = v_isSharedCheck_4703_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4685_);
                        leanh::lean_dec(v_b_4682_);
                        v___x_4687_ = leanh::lean_box(0);
                        v_isShared_4688_ = v_isSharedCheck_4703_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4689_ = lean_array_uget_borrowed(v_as_4679_, v_i_4681_);
                v_msg_4690_ = leanh::lean_ctor_get(v_a_4689_, 1);
                v___x_4691_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___x_4675_);
                v___x_4692_ = l_Lean_FileMap_toPosition(v___x_4675_, v___x_4676_);
                v___x_4693_ = 0;
                v___x_4694_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0;
                leanh::lean_inc_ref(v_msg_4690_);
                leanh::lean_inc_ref(v___x_4677_);
                v___x_4695_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_4695_, 0, v___x_4677_);
                leanh::lean_ctor_set(v___x_4695_, 1, v___x_4692_);
                leanh::lean_ctor_set(v___x_4695_, 2, v___x_4691_);
                leanh::lean_ctor_set(v___x_4695_, 3, v___x_4694_);
                leanh::lean_ctor_set(v___x_4695_, 4, v_msg_4690_);
                leanh::lean_ctor_set_uint8(
                    v___x_4695_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v_val_4678_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4695_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_4693_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4695_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_val_4678_,
                );
                v___x_4696_ = l_Lean_MessageLog_add(v___x_4695_, v_snd_4685_);
                if v_isShared_4688_ == 0 {
                    leanh::lean_ctor_set(v___x_4687_, 1, v___x_4696_);
                    leanh::lean_ctor_set(v___x_4687_, 0, v___x_4691_);
                    v___x_4698_ = v___x_4687_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4702_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 0, v___x_4691_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 1, v___x_4696_);
                    v___x_4698_ = v_reuseFailAlloc_4702_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4699_ = 1usize;
                v___x_4700_ = lean_usize_add(v_i_4681_, v___x_4699_);
                v_i_4681_ = v___x_4700_;
                v_b_4682_ = v___x_4698_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5___boxed(
    mut v___x_4705_: *mut leanh::LeanObject,
    mut v___x_4706_: *mut leanh::LeanObject,
    mut v___x_4707_: *mut leanh::LeanObject,
    mut v_val_4708_: *mut leanh::LeanObject,
    mut v_as_4709_: *mut leanh::LeanObject,
    mut v_sz_4710_: *mut leanh::LeanObject,
    mut v_i_4711_: *mut leanh::LeanObject,
    mut v_b_4712_: *mut leanh::LeanObject,
    mut v___y_4713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_44570__boxed_4714_: u8 = 0;
    let mut v_sz_boxed_4715_: usize = 0;
    let mut v_i_boxed_4716_: usize = 0;
    let mut v_res_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_44570__boxed_4714_ = (leanh::lean_unbox(v_val_4708_) as u8);
    v_sz_boxed_4715_ = leanh::lean_unbox_usize(v_sz_4710_);
    leanh::lean_dec(v_sz_4710_);
    v_i_boxed_4716_ = leanh::lean_unbox_usize(v_i_4711_);
    leanh::lean_dec(v_i_4711_);
    v_res_4717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_4705_, v___x_4706_, v___x_4707_, v_val_44570__boxed_4714_, v_as_4709_, v_sz_boxed_4715_, v_i_boxed_4716_, v_b_4712_);
    leanh::lean_dec_ref(v_as_4709_);
    leanh::lean_dec(v___x_4706_);
    return v_res_4717_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(
    mut v___x_4718_: *mut leanh::LeanObject,
    mut v___x_4719_: *mut leanh::LeanObject,
    mut v___x_4720_: *mut leanh::LeanObject,
    mut v_val_4721_: u8,
    mut v_as_4722_: *mut leanh::LeanObject,
    mut v_sz_4723_: usize,
    mut v_i_4724_: usize,
    mut v_b_4725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4727_: u8 = 0;
    let mut v_snd_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4731_: u8 = 0;
    let mut v_a_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: u8 = 0;
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: usize = 0;
    let mut v___x_4743_: usize = 0;
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4746_: u8 = 0;
    let mut v_unused_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4727_ = lean_usize_dec_lt(v_i_4724_, v_sz_4723_);
                if v___x_4727_ == 0 {
                    leanh::lean_dec_ref(v___x_4720_);
                    leanh::lean_dec_ref(v___x_4718_);
                    return v_b_4725_;
                } else {
                    v_snd_4728_ = leanh::lean_ctor_get(v_b_4725_, 1);
                    v_isSharedCheck_4746_ = (!leanh::lean_is_exclusive(v_b_4725_)) as u8;
                    if v_isSharedCheck_4746_ == 0 {
                        v_unused_4747_ = leanh::lean_ctor_get(v_b_4725_, 0);
                        leanh::lean_dec(v_unused_4747_);
                        v___x_4730_ = v_b_4725_;
                        v_isShared_4731_ = v_isSharedCheck_4746_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4728_);
                        leanh::lean_dec(v_b_4725_);
                        v___x_4730_ = leanh::lean_box(0);
                        v_isShared_4731_ = v_isSharedCheck_4746_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4732_ = lean_array_uget_borrowed(v_as_4722_, v_i_4724_);
                v_msg_4733_ = leanh::lean_ctor_get(v_a_4732_, 1);
                v___x_4734_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___x_4718_);
                v___x_4735_ = l_Lean_FileMap_toPosition(v___x_4718_, v___x_4719_);
                v___x_4736_ = 0;
                v___x_4737_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0;
                leanh::lean_inc_ref(v_msg_4733_);
                leanh::lean_inc_ref(v___x_4720_);
                v___x_4738_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_4738_, 0, v___x_4720_);
                leanh::lean_ctor_set(v___x_4738_, 1, v___x_4735_);
                leanh::lean_ctor_set(v___x_4738_, 2, v___x_4734_);
                leanh::lean_ctor_set(v___x_4738_, 3, v___x_4737_);
                leanh::lean_ctor_set(v___x_4738_, 4, v_msg_4733_);
                leanh::lean_ctor_set_uint8(
                    v___x_4738_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v_val_4721_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4738_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_4736_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4738_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_val_4721_,
                );
                v___x_4739_ = l_Lean_MessageLog_add(v___x_4738_, v_snd_4728_);
                if v_isShared_4731_ == 0 {
                    leanh::lean_ctor_set(v___x_4730_, 1, v___x_4739_);
                    leanh::lean_ctor_set(v___x_4730_, 0, v___x_4734_);
                    v___x_4741_ = v___x_4730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4745_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4745_, 1, v___x_4739_);
                    v___x_4741_ = v_reuseFailAlloc_4745_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4742_ = 1usize;
                v___x_4743_ = lean_usize_add(v_i_4724_, v___x_4742_);
                v___x_4744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_4718_, v___x_4719_, v___x_4720_, v_val_4721_, v_as_4722_, v_sz_4723_, v___x_4743_, v___x_4741_);
                return v___x_4744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3___boxed(
    mut v___x_4748_: *mut leanh::LeanObject,
    mut v___x_4749_: *mut leanh::LeanObject,
    mut v___x_4750_: *mut leanh::LeanObject,
    mut v_val_4751_: *mut leanh::LeanObject,
    mut v_as_4752_: *mut leanh::LeanObject,
    mut v_sz_4753_: *mut leanh::LeanObject,
    mut v_i_4754_: *mut leanh::LeanObject,
    mut v_b_4755_: *mut leanh::LeanObject,
    mut v___y_4756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_44622__boxed_4757_: u8 = 0;
    let mut v_sz_boxed_4758_: usize = 0;
    let mut v_i_boxed_4759_: usize = 0;
    let mut v_res_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_44622__boxed_4757_ = (leanh::lean_unbox(v_val_4751_) as u8);
    v_sz_boxed_4758_ = leanh::lean_unbox_usize(v_sz_4753_);
    leanh::lean_dec(v_sz_4753_);
    v_i_boxed_4759_ = leanh::lean_unbox_usize(v_i_4754_);
    leanh::lean_dec(v_i_4754_);
    v_res_4760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_4748_, v___x_4749_, v___x_4750_, v_val_44622__boxed_4757_, v_as_4752_, v_sz_boxed_4758_, v_i_boxed_4759_, v_b_4755_);
    leanh::lean_dec_ref(v_as_4752_);
    leanh::lean_dec(v___x_4749_);
    return v_res_4760_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(
    mut v_init_4761_: *mut leanh::LeanObject,
    mut v___x_4762_: *mut leanh::LeanObject,
    mut v___x_4763_: *mut leanh::LeanObject,
    mut v___x_4764_: *mut leanh::LeanObject,
    mut v_val_4765_: u8,
    mut v_n_4766_: *mut leanh::LeanObject,
    mut v_b_4767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_n_4766_) == 0 {
        let mut v_cs_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4772_: usize = 0;
        let mut v___x_4773_: usize = 0;
        let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_cs_4769_ = leanh::lean_ctor_get(v_n_4766_, 0);
        v___x_4770_ = leanh::lean_box(0);
        v___x_4771_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4771_, 0, v___x_4770_);
        leanh::lean_ctor_set(v___x_4771_, 1, v_b_4767_);
        v_sz_4772_ = lean_array_size(v_cs_4769_);
        v___x_4773_ = 0usize;
        v___x_4774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v_init_4761_, v___x_4762_, v___x_4763_, v___x_4764_, v_val_4765_, v_cs_4769_, v_sz_4772_, v___x_4773_, v___x_4771_);
        v_fst_4775_ = leanh::lean_ctor_get(v___x_4774_, 0);
        leanh::lean_inc(v_fst_4775_);
        if leanh::lean_obj_tag(v_fst_4775_) == 0 {
            let mut v_snd_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_snd_4776_ = leanh::lean_ctor_get(v___x_4774_, 1);
            leanh::lean_inc(v_snd_4776_);
            leanh::lean_dec_ref(v___x_4774_);
            v___x_4777_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_4777_, 0, v_snd_4776_);
            return v___x_4777_;
        } else {
            let mut v_val_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_4774_);
            v_val_4778_ = leanh::lean_ctor_get(v_fst_4775_, 0);
            leanh::lean_inc(v_val_4778_);
            leanh::lean_dec_ref_known(v_fst_4775_, 1);
            return v_val_4778_;
        }
    } else {
        let mut v_vs_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4782_: usize = 0;
        let mut v___x_4783_: usize = 0;
        let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_vs_4779_ = leanh::lean_ctor_get(v_n_4766_, 0);
        v___x_4780_ = leanh::lean_box(0);
        v___x_4781_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4781_, 0, v___x_4780_);
        leanh::lean_ctor_set(v___x_4781_, 1, v_b_4767_);
        v_sz_4782_ = lean_array_size(v_vs_4779_);
        v___x_4783_ = 0usize;
        v___x_4784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_4762_, v___x_4763_, v___x_4764_, v_val_4765_, v_vs_4779_, v_sz_4782_, v___x_4783_, v___x_4781_);
        v_fst_4785_ = leanh::lean_ctor_get(v___x_4784_, 0);
        leanh::lean_inc(v_fst_4785_);
        if leanh::lean_obj_tag(v_fst_4785_) == 0 {
            let mut v_snd_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_snd_4786_ = leanh::lean_ctor_get(v___x_4784_, 1);
            leanh::lean_inc(v_snd_4786_);
            leanh::lean_dec_ref(v___x_4784_);
            v___x_4787_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_4787_, 0, v_snd_4786_);
            return v___x_4787_;
        } else {
            let mut v_val_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_4784_);
            v_val_4788_ = leanh::lean_ctor_get(v_fst_4785_, 0);
            leanh::lean_inc(v_val_4788_);
            leanh::lean_dec_ref_known(v_fst_4785_, 1);
            return v_val_4788_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(
    mut v_init_4789_: *mut leanh::LeanObject,
    mut v___x_4790_: *mut leanh::LeanObject,
    mut v___x_4791_: *mut leanh::LeanObject,
    mut v___x_4792_: *mut leanh::LeanObject,
    mut v_val_4793_: u8,
    mut v_as_4794_: *mut leanh::LeanObject,
    mut v_sz_4795_: usize,
    mut v_i_4796_: usize,
    mut v_b_4797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4799_: u8 = 0;
    let mut v_snd_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4803_: u8 = 0;
    let mut v_a_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: usize = 0;
    let mut v___x_4815_: usize = 0;
    let mut v_reuseFailAlloc_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4818_: u8 = 0;
    let mut v_unused_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4799_ = lean_usize_dec_lt(v_i_4796_, v_sz_4795_);
                if v___x_4799_ == 0 {
                    leanh::lean_dec_ref(v___x_4792_);
                    leanh::lean_dec_ref(v___x_4790_);
                    return v_b_4797_;
                } else {
                    v_snd_4800_ = leanh::lean_ctor_get(v_b_4797_, 1);
                    v_isSharedCheck_4818_ = (!leanh::lean_is_exclusive(v_b_4797_)) as u8;
                    if v_isSharedCheck_4818_ == 0 {
                        v_unused_4819_ = leanh::lean_ctor_get(v_b_4797_, 0);
                        leanh::lean_dec(v_unused_4819_);
                        v___x_4802_ = v_b_4797_;
                        v_isShared_4803_ = v_isSharedCheck_4818_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4800_);
                        leanh::lean_dec(v_b_4797_);
                        v___x_4802_ = leanh::lean_box(0);
                        v_isShared_4803_ = v_isSharedCheck_4818_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4804_ = lean_array_uget_borrowed(v_as_4794_, v_i_4796_);
                leanh::lean_inc(v_snd_4800_);
                leanh::lean_inc_ref(v___x_4792_);
                leanh::lean_inc_ref(v___x_4790_);
                v___x_4805_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_4789_, v___x_4790_, v___x_4791_, v___x_4792_, v_val_4793_, v_a_4804_, v_snd_4800_);
                if leanh::lean_obj_tag(v___x_4805_) == 0 {
                    leanh::lean_dec_ref(v___x_4792_);
                    leanh::lean_dec_ref(v___x_4790_);
                    v___x_4806_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4806_, 0, v___x_4805_);
                    if v_isShared_4803_ == 0 {
                        leanh::lean_ctor_set(v___x_4802_, 0, v___x_4806_);
                        v___x_4808_ = v___x_4802_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4809_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4806_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4809_, 1, v_snd_4800_);
                        v___x_4808_ = v_reuseFailAlloc_4809_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_4800_);
                    v_a_4810_ = leanh::lean_ctor_get(v___x_4805_, 0);
                    leanh::lean_inc(v_a_4810_);
                    leanh::lean_dec_ref_known(v___x_4805_, 1);
                    v___x_4811_ = leanh::lean_box(0);
                    if v_isShared_4803_ == 0 {
                        leanh::lean_ctor_set(v___x_4802_, 1, v_a_4810_);
                        leanh::lean_ctor_set(v___x_4802_, 0, v___x_4811_);
                        v___x_4813_ = v___x_4802_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4817_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4811_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 1, v_a_4810_);
                        v___x_4813_ = v_reuseFailAlloc_4817_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4808_;
            }
            3 => {
                v___x_4814_ = 1usize;
                v___x_4815_ = lean_usize_add(v_i_4796_, v___x_4814_);
                v_i_4796_ = v___x_4815_;
                v_b_4797_ = v___x_4813_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2___boxed(
    mut v_init_4820_: *mut leanh::LeanObject,
    mut v___x_4821_: *mut leanh::LeanObject,
    mut v___x_4822_: *mut leanh::LeanObject,
    mut v___x_4823_: *mut leanh::LeanObject,
    mut v_val_4824_: *mut leanh::LeanObject,
    mut v_as_4825_: *mut leanh::LeanObject,
    mut v_sz_4826_: *mut leanh::LeanObject,
    mut v_i_4827_: *mut leanh::LeanObject,
    mut v_b_4828_: *mut leanh::LeanObject,
    mut v___y_4829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_44673__boxed_4830_: u8 = 0;
    let mut v_sz_boxed_4831_: usize = 0;
    let mut v_i_boxed_4832_: usize = 0;
    let mut v_res_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_44673__boxed_4830_ = (leanh::lean_unbox(v_val_4824_) as u8);
    v_sz_boxed_4831_ = leanh::lean_unbox_usize(v_sz_4826_);
    leanh::lean_dec(v_sz_4826_);
    v_i_boxed_4832_ = leanh::lean_unbox_usize(v_i_4827_);
    leanh::lean_dec(v_i_4827_);
    v_res_4833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v_init_4820_, v___x_4821_, v___x_4822_, v___x_4823_, v_val_44673__boxed_4830_, v_as_4825_, v_sz_boxed_4831_, v_i_boxed_4832_, v_b_4828_);
    leanh::lean_dec_ref(v_as_4825_);
    leanh::lean_dec(v___x_4822_);
    leanh::lean_dec_ref(v_init_4820_);
    return v_res_4833_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1___boxed(
    mut v_init_4834_: *mut leanh::LeanObject,
    mut v___x_4835_: *mut leanh::LeanObject,
    mut v___x_4836_: *mut leanh::LeanObject,
    mut v___x_4837_: *mut leanh::LeanObject,
    mut v_val_4838_: *mut leanh::LeanObject,
    mut v_n_4839_: *mut leanh::LeanObject,
    mut v_b_4840_: *mut leanh::LeanObject,
    mut v___y_4841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_44689__boxed_4842_: u8 = 0;
    let mut v_res_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_44689__boxed_4842_ = (leanh::lean_unbox(v_val_4838_) as u8);
    v_res_4843_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_4834_, v___x_4835_, v___x_4836_, v___x_4837_, v_val_44689__boxed_4842_, v_n_4839_, v_b_4840_);
    leanh::lean_dec_ref(v_n_4839_);
    leanh::lean_dec(v___x_4836_);
    leanh::lean_dec_ref(v_init_4834_);
    return v_res_4843_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(
    mut v___x_4844_: *mut leanh::LeanObject,
    mut v___x_4845_: *mut leanh::LeanObject,
    mut v___x_4846_: *mut leanh::LeanObject,
    mut v_val_4847_: u8,
    mut v_as_4848_: *mut leanh::LeanObject,
    mut v_sz_4849_: usize,
    mut v_i_4850_: usize,
    mut v_b_4851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4853_: u8 = 0;
    let mut v_snd_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4857_: u8 = 0;
    let mut v_a_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: u8 = 0;
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: usize = 0;
    let mut v___x_4869_: usize = 0;
    let mut v_reuseFailAlloc_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4872_: u8 = 0;
    let mut v_unused_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4853_ = lean_usize_dec_lt(v_i_4850_, v_sz_4849_);
                if v___x_4853_ == 0 {
                    leanh::lean_dec_ref(v___x_4846_);
                    leanh::lean_dec_ref(v___x_4844_);
                    return v_b_4851_;
                } else {
                    v_snd_4854_ = leanh::lean_ctor_get(v_b_4851_, 1);
                    v_isSharedCheck_4872_ = (!leanh::lean_is_exclusive(v_b_4851_)) as u8;
                    if v_isSharedCheck_4872_ == 0 {
                        v_unused_4873_ = leanh::lean_ctor_get(v_b_4851_, 0);
                        leanh::lean_dec(v_unused_4873_);
                        v___x_4856_ = v_b_4851_;
                        v_isShared_4857_ = v_isSharedCheck_4872_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4854_);
                        leanh::lean_dec(v_b_4851_);
                        v___x_4856_ = leanh::lean_box(0);
                        v_isShared_4857_ = v_isSharedCheck_4872_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4858_ = lean_array_uget_borrowed(v_as_4848_, v_i_4850_);
                v_msg_4859_ = leanh::lean_ctor_get(v_a_4858_, 1);
                v___x_4860_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___x_4844_);
                v___x_4861_ = l_Lean_FileMap_toPosition(v___x_4844_, v___x_4845_);
                v___x_4862_ = 0;
                v___x_4863_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0;
                leanh::lean_inc_ref(v_msg_4859_);
                leanh::lean_inc_ref(v___x_4846_);
                v___x_4864_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_4864_, 0, v___x_4846_);
                leanh::lean_ctor_set(v___x_4864_, 1, v___x_4861_);
                leanh::lean_ctor_set(v___x_4864_, 2, v___x_4860_);
                leanh::lean_ctor_set(v___x_4864_, 3, v___x_4863_);
                leanh::lean_ctor_set(v___x_4864_, 4, v_msg_4859_);
                leanh::lean_ctor_set_uint8(
                    v___x_4864_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v_val_4847_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4864_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_4862_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4864_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_val_4847_,
                );
                v___x_4865_ = l_Lean_MessageLog_add(v___x_4864_, v_snd_4854_);
                if v_isShared_4857_ == 0 {
                    leanh::lean_ctor_set(v___x_4856_, 1, v___x_4865_);
                    leanh::lean_ctor_set(v___x_4856_, 0, v___x_4860_);
                    v___x_4867_ = v___x_4856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4871_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4871_, 0, v___x_4860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4871_, 1, v___x_4865_);
                    v___x_4867_ = v_reuseFailAlloc_4871_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4868_ = 1usize;
                v___x_4869_ = lean_usize_add(v_i_4850_, v___x_4868_);
                v_i_4850_ = v___x_4869_;
                v_b_4851_ = v___x_4867_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5___boxed(
    mut v___x_4874_: *mut leanh::LeanObject,
    mut v___x_4875_: *mut leanh::LeanObject,
    mut v___x_4876_: *mut leanh::LeanObject,
    mut v_val_4877_: *mut leanh::LeanObject,
    mut v_as_4878_: *mut leanh::LeanObject,
    mut v_sz_4879_: *mut leanh::LeanObject,
    mut v_i_4880_: *mut leanh::LeanObject,
    mut v_b_4881_: *mut leanh::LeanObject,
    mut v___y_4882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_44771__boxed_4883_: u8 = 0;
    let mut v_sz_boxed_4884_: usize = 0;
    let mut v_i_boxed_4885_: usize = 0;
    let mut v_res_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_44771__boxed_4883_ = (leanh::lean_unbox(v_val_4877_) as u8);
    v_sz_boxed_4884_ = leanh::lean_unbox_usize(v_sz_4879_);
    leanh::lean_dec(v_sz_4879_);
    v_i_boxed_4885_ = leanh::lean_unbox_usize(v_i_4880_);
    leanh::lean_dec(v_i_4880_);
    v_res_4886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_4874_, v___x_4875_, v___x_4876_, v_val_44771__boxed_4883_, v_as_4878_, v_sz_boxed_4884_, v_i_boxed_4885_, v_b_4881_);
    leanh::lean_dec_ref(v_as_4878_);
    leanh::lean_dec(v___x_4875_);
    return v_res_4886_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(
    mut v___x_4887_: *mut leanh::LeanObject,
    mut v___x_4888_: *mut leanh::LeanObject,
    mut v___x_4889_: *mut leanh::LeanObject,
    mut v_val_4890_: u8,
    mut v_as_4891_: *mut leanh::LeanObject,
    mut v_sz_4892_: usize,
    mut v_i_4893_: usize,
    mut v_b_4894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4896_: u8 = 0;
    let mut v_snd_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4900_: u8 = 0;
    let mut v_a_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: u8 = 0;
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: usize = 0;
    let mut v___x_4912_: usize = 0;
    let mut v___x_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4915_: u8 = 0;
    let mut v_unused_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4896_ = lean_usize_dec_lt(v_i_4893_, v_sz_4892_);
                if v___x_4896_ == 0 {
                    leanh::lean_dec_ref(v___x_4889_);
                    leanh::lean_dec_ref(v___x_4887_);
                    return v_b_4894_;
                } else {
                    v_snd_4897_ = leanh::lean_ctor_get(v_b_4894_, 1);
                    v_isSharedCheck_4915_ = (!leanh::lean_is_exclusive(v_b_4894_)) as u8;
                    if v_isSharedCheck_4915_ == 0 {
                        v_unused_4916_ = leanh::lean_ctor_get(v_b_4894_, 0);
                        leanh::lean_dec(v_unused_4916_);
                        v___x_4899_ = v_b_4894_;
                        v_isShared_4900_ = v_isSharedCheck_4915_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4897_);
                        leanh::lean_dec(v_b_4894_);
                        v___x_4899_ = leanh::lean_box(0);
                        v_isShared_4900_ = v_isSharedCheck_4915_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4901_ = lean_array_uget_borrowed(v_as_4891_, v_i_4893_);
                v_msg_4902_ = leanh::lean_ctor_get(v_a_4901_, 1);
                v___x_4903_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___x_4887_);
                v___x_4904_ = l_Lean_FileMap_toPosition(v___x_4887_, v___x_4888_);
                v___x_4905_ = 0;
                v___x_4906_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0;
                leanh::lean_inc_ref(v_msg_4902_);
                leanh::lean_inc_ref(v___x_4889_);
                v___x_4907_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_4907_, 0, v___x_4889_);
                leanh::lean_ctor_set(v___x_4907_, 1, v___x_4904_);
                leanh::lean_ctor_set(v___x_4907_, 2, v___x_4903_);
                leanh::lean_ctor_set(v___x_4907_, 3, v___x_4906_);
                leanh::lean_ctor_set(v___x_4907_, 4, v_msg_4902_);
                leanh::lean_ctor_set_uint8(
                    v___x_4907_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v_val_4890_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4907_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_4905_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4907_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_val_4890_,
                );
                v___x_4908_ = l_Lean_MessageLog_add(v___x_4907_, v_snd_4897_);
                if v_isShared_4900_ == 0 {
                    leanh::lean_ctor_set(v___x_4899_, 1, v___x_4908_);
                    leanh::lean_ctor_set(v___x_4899_, 0, v___x_4903_);
                    v___x_4910_ = v___x_4899_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4914_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4914_, 1, v___x_4908_);
                    v___x_4910_ = v_reuseFailAlloc_4914_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4911_ = 1usize;
                v___x_4912_ = lean_usize_add(v_i_4893_, v___x_4911_);
                v___x_4913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_4887_, v___x_4888_, v___x_4889_, v_val_4890_, v_as_4891_, v_sz_4892_, v___x_4912_, v___x_4910_);
                return v___x_4913_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2___boxed(
    mut v___x_4917_: *mut leanh::LeanObject,
    mut v___x_4918_: *mut leanh::LeanObject,
    mut v___x_4919_: *mut leanh::LeanObject,
    mut v_val_4920_: *mut leanh::LeanObject,
    mut v_as_4921_: *mut leanh::LeanObject,
    mut v_sz_4922_: *mut leanh::LeanObject,
    mut v_i_4923_: *mut leanh::LeanObject,
    mut v_b_4924_: *mut leanh::LeanObject,
    mut v___y_4925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_44823__boxed_4926_: u8 = 0;
    let mut v_sz_boxed_4927_: usize = 0;
    let mut v_i_boxed_4928_: usize = 0;
    let mut v_res_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_44823__boxed_4926_ = (leanh::lean_unbox(v_val_4920_) as u8);
    v_sz_boxed_4927_ = leanh::lean_unbox_usize(v_sz_4922_);
    leanh::lean_dec(v_sz_4922_);
    v_i_boxed_4928_ = leanh::lean_unbox_usize(v_i_4923_);
    leanh::lean_dec(v_i_4923_);
    v_res_4929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_4917_, v___x_4918_, v___x_4919_, v_val_44823__boxed_4926_, v_as_4921_, v_sz_boxed_4927_, v_i_boxed_4928_, v_b_4924_);
    leanh::lean_dec_ref(v_as_4921_);
    leanh::lean_dec(v___x_4918_);
    return v_res_4929_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(
    mut v___x_4930_: *mut leanh::LeanObject,
    mut v___x_4931_: *mut leanh::LeanObject,
    mut v___x_4932_: *mut leanh::LeanObject,
    mut v_val_4933_: u8,
    mut v_t_4934_: *mut leanh::LeanObject,
    mut v_init_4935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_4937_ = leanh::lean_ctor_get(v_t_4934_, 0);
    v_tail_4938_ = leanh::lean_ctor_get(v_t_4934_, 1);
    leanh::lean_inc_ref(v___x_4932_);
    leanh::lean_inc_ref(v___x_4930_);
    leanh::lean_inc_ref(v_init_4935_);
    v___x_4939_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_4935_, v___x_4930_, v___x_4931_, v___x_4932_, v_val_4933_, v_root_4937_, v_init_4935_);
    leanh::lean_dec_ref(v_init_4935_);
    if leanh::lean_obj_tag(v___x_4939_) == 0 {
        let mut v_a_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_4932_);
        leanh::lean_dec_ref(v___x_4930_);
        v_a_4940_ = leanh::lean_ctor_get(v___x_4939_, 0);
        leanh::lean_inc(v_a_4940_);
        leanh::lean_dec_ref_known(v___x_4939_, 1);
        return v_a_4940_;
    } else {
        let mut v_a_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4944_: usize = 0;
        let mut v___x_4945_: usize = 0;
        let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4941_ = leanh::lean_ctor_get(v___x_4939_, 0);
        leanh::lean_inc(v_a_4941_);
        leanh::lean_dec_ref_known(v___x_4939_, 1);
        v___x_4942_ = leanh::lean_box(0);
        v___x_4943_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4943_, 0, v___x_4942_);
        leanh::lean_ctor_set(v___x_4943_, 1, v_a_4941_);
        v_sz_4944_ = lean_array_size(v_tail_4938_);
        v___x_4945_ = 0usize;
        v___x_4946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_4930_, v___x_4931_, v___x_4932_, v_val_4933_, v_tail_4938_, v_sz_4944_, v___x_4945_, v___x_4943_);
        v_fst_4947_ = leanh::lean_ctor_get(v___x_4946_, 0);
        leanh::lean_inc(v_fst_4947_);
        if leanh::lean_obj_tag(v_fst_4947_) == 0 {
            let mut v_snd_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_snd_4948_ = leanh::lean_ctor_get(v___x_4946_, 1);
            leanh::lean_inc(v_snd_4948_);
            leanh::lean_dec_ref(v___x_4946_);
            return v_snd_4948_;
        } else {
            let mut v_val_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_4946_);
            v_val_4949_ = leanh::lean_ctor_get(v_fst_4947_, 0);
            leanh::lean_inc(v_val_4949_);
            leanh::lean_dec_ref_known(v_fst_4947_, 1);
            return v_val_4949_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1___boxed(
    mut v___x_4950_: *mut leanh::LeanObject,
    mut v___x_4951_: *mut leanh::LeanObject,
    mut v___x_4952_: *mut leanh::LeanObject,
    mut v_val_4953_: *mut leanh::LeanObject,
    mut v_t_4954_: *mut leanh::LeanObject,
    mut v_init_4955_: *mut leanh::LeanObject,
    mut v___y_4956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_44874__boxed_4957_: u8 = 0;
    let mut v_res_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_44874__boxed_4957_ = (leanh::lean_unbox(v_val_4953_) as u8);
    v_res_4958_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v___x_4950_, v___x_4951_, v___x_4952_, v_val_44874__boxed_4957_, v_t_4954_, v_init_4955_);
    leanh::lean_dec_ref(v_t_4954_);
    leanh::lean_dec(v___x_4951_);
    return v_res_4958_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4959_ = leanh::lean_unsigned_to_nat(1);
    v___x_4960_ = l_Lean_firstFrontendMacroScope;
    v___x_4961_ = lean_nat_add(v___x_4960_, v___x_4959_);
    return v___x_4961_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4968_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4968_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4969_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
    v___x_4970_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4970_, 0, v___x_4969_);
    return v___x_4970_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4971_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
    v___x_4972_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4972_, 0, v___x_4971_);
    leanh::lean_ctor_set(v___x_4972_, 1, v___x_4971_);
    return v___x_4972_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(
    mut v___x_4973_: *mut leanh::LeanObject,
    mut v___x_4974_: *mut leanh::LeanObject,
    mut v___x_4975_: *mut leanh::LeanObject,
    mut v___x_4976_: usize,
    mut v___x_4977_: u8,
    mut v_env_4978_: *mut leanh::LeanObject,
    mut v___x_4979_: *mut leanh::LeanObject,
    mut v___x_4980_: *mut leanh::LeanObject,
    mut v_a_4981_: *mut leanh::LeanObject,
    mut v_opts_4982_: *mut leanh::LeanObject,
    mut v___x_4983_: *mut leanh::LeanObject,
    mut v_pos_4984_: *mut leanh::LeanObject,
    mut v_val_4985_: u8,
    mut v___x_4986_: *mut leanh::LeanObject,
    mut v___x_4987_: *mut leanh::LeanObject,
    mut v___x_4988_: *mut leanh::LeanObject,
    mut v___x_4989_: *mut leanh::LeanObject,
    mut v___x_4990_: u8,
    mut v_x_4991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcessingContext_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: u8 = 0;
    let mut v_fileName_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5032_: u8 = 0;
    let mut v_inheritedTraceOptions_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5051_: u8 = 0;
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5063_: u8 = 0;
    let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5069_: u8 = 0;
    let mut v_unused_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4993_ = l_Lean_firstFrontendMacroScope;
                v___x_4994_ = leanh::lean_unsigned_to_nat(1);
                v___x_4995_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
                v___x_4996_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3;
                v___x_4997_ = leanh::lean_box(0);
                leanh::lean_inc(v___x_4973_);
                v___x_4998_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4998_, 0, v___x_4973_);
                leanh::lean_ctor_set(v___x_4998_, 1, v___x_4994_);
                leanh::lean_ctor_set(v___x_4998_, 2, v___x_4997_);
                v___x_4999_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
                v___x_5000_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6);
                v___x_5001_ = lean_mk_empty_array_with_capacity(v___x_4974_);
                leanh::lean_inc_ref(v___x_5001_);
                v___x_5002_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5002_, 0, v___x_5001_);
                leanh::lean_inc_n(v___x_4975_, 2);
                v___x_5003_ =
                    leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                leanh::lean_ctor_set(v___x_5003_, 0, v___x_5002_);
                leanh::lean_ctor_set(v___x_5003_, 1, v___x_5001_);
                leanh::lean_ctor_set(v___x_5003_, 2, v___x_4975_);
                leanh::lean_ctor_set(v___x_5003_, 3, v___x_4975_);
                leanh::lean_ctor_set_usize(v___x_5003_, 4, v___x_4976_);
                v___x_5004_ = l_Lean_NameSet_empty;
                leanh::lean_inc_ref_n(v___x_5003_, 2);
                v___x_5005_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5005_, 0, v___x_5003_);
                leanh::lean_ctor_set(v___x_5005_, 1, v___x_5003_);
                leanh::lean_ctor_set(v___x_5005_, 2, v___x_5004_);
                v___x_5006_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_5006_, 0, v___x_4999_);
                leanh::lean_ctor_set(v___x_5006_, 1, v___x_4999_);
                leanh::lean_ctor_set(v___x_5006_, 2, v___x_5003_);
                leanh::lean_ctor_set_uint8(
                    v___x_5006_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4977_,
                );
                v___x_5007_ = lean_mk_empty_array_with_capacity(v___x_4975_);
                leanh::lean_inc_ref(v___x_5007_);
                leanh::lean_inc_ref(v___x_4979_);
                v___x_5008_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                leanh::lean_ctor_set(v___x_5008_, 0, v_env_4978_);
                leanh::lean_ctor_set(v___x_5008_, 1, v___x_4995_);
                leanh::lean_ctor_set(v___x_5008_, 2, v___x_4996_);
                leanh::lean_ctor_set(v___x_5008_, 3, v___x_4998_);
                leanh::lean_ctor_set(v___x_5008_, 4, v___x_4979_);
                leanh::lean_ctor_set(v___x_5008_, 5, v___x_5000_);
                leanh::lean_ctor_set(v___x_5008_, 6, v___x_5005_);
                leanh::lean_ctor_set(v___x_5008_, 7, v___x_5006_);
                leanh::lean_ctor_set(v___x_5008_, 8, v___x_5007_);
                v___x_5009_ = lean_st_mk_ref(v___x_5008_);
                v___x_5010_ = lean_st_ref_get(v___x_4980_);
                v___x_5011_ = lean_st_ref_get(v___x_5009_);
                v_toProcessingContext_5012_ = leanh::lean_ctor_get(v_a_4981_, 0);
                v_fileName_5013_ = leanh::lean_ctor_get(v_toProcessingContext_5012_, 1);
                v_fileMap_5014_ = leanh::lean_ctor_get(v_toProcessingContext_5012_, 2);
                v_env_5015_ = leanh::lean_ctor_get(v___x_5011_, 0);
                leanh::lean_inc_ref(v_env_5015_);
                leanh::lean_dec(v___x_5011_);
                v___x_5016_ = leanh::lean_box(0);
                v___x_5017_ = l_Lean_Core_getMaxHeartbeats(v_opts_4982_);
                v___x_5018_ = l_Lean_diagnostics;
                v___x_5019_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_4982_, v___x_5018_);
                v___x_5071_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5015_);
                leanh::lean_dec_ref(v_env_5015_);
                if v___x_5071_ == 0 {
                    if v___x_5019_ == 0 {
                        v___y_5051_ = v___x_4990_;
                        state = 2;
                        continue;
                    } else {
                        v___y_5051_ = v___x_5071_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___y_5051_ = v___x_5019_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5035_ = l_Lean_maxRecDepth;
                v___x_5036_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(v_opts_4982_, v___x_5035_);
                leanh::lean_inc(v_currMacroScope_5030_);
                leanh::lean_inc(v_openDecls_5026_);
                leanh::lean_inc(v_ref_5024_);
                v___x_5037_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_5037_, 0, v_fileName_5021_);
                leanh::lean_ctor_set(v___x_5037_, 1, v_fileMap_5022_);
                leanh::lean_ctor_set(v___x_5037_, 2, v_opts_4982_);
                leanh::lean_ctor_set(v___x_5037_, 3, v_currRecDepth_5023_);
                leanh::lean_ctor_set(v___x_5037_, 4, v___x_5036_);
                leanh::lean_ctor_set(v___x_5037_, 5, v_ref_5024_);
                leanh::lean_ctor_set(v___x_5037_, 6, v_currNamespace_5025_);
                leanh::lean_ctor_set(v___x_5037_, 7, v_openDecls_5026_);
                leanh::lean_ctor_set(v___x_5037_, 8, v_initHeartbeats_5027_);
                leanh::lean_ctor_set(v___x_5037_, 9, v_maxHeartbeats_5028_);
                leanh::lean_ctor_set(v___x_5037_, 10, v_quotContext_5029_);
                leanh::lean_ctor_set(v___x_5037_, 11, v_currMacroScope_5030_);
                leanh::lean_ctor_set(v___x_5037_, 12, v_cancelTk_x3f_5031_);
                leanh::lean_ctor_set(v___x_5037_, 13, v_inheritedTraceOptions_5033_);
                leanh::lean_ctor_set_uint8(
                    v___x_5037_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___x_5019_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5037_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5032_,
                );
                v___x_5038_ =
                    l_Lean_Language_SnapshotTree_trace(v___x_4983_, v___x_5037_, v___y_5034_);
                leanh::lean_dec(v___y_5034_);
                leanh::lean_dec_ref_known(v___x_5037_, 14);
                if leanh::lean_obj_tag(v___x_5038_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5038_, 1);
                    leanh::lean_dec_ref(v___x_4988_);
                    v___x_5039_ = lean_st_ref_get(v___x_5009_);
                    leanh::lean_dec(v___x_5009_);
                    v_traceState_5040_ = leanh::lean_ctor_get(v___x_5039_, 4);
                    leanh::lean_inc_ref(v_traceState_5040_);
                    leanh::lean_dec(v___x_5039_);
                    v_traces_5041_ = leanh::lean_ctor_get(v_traceState_5040_, 0);
                    leanh::lean_inc_ref(v_traces_5041_);
                    leanh::lean_dec_ref(v_traceState_5040_);
                    v___x_5042_ = l_Lean_MessageLog_empty;
                    leanh::lean_inc_ref(v_fileName_5013_);
                    leanh::lean_inc_ref(v_fileMap_5014_);
                    v___x_5043_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v_fileMap_5014_, v_pos_4984_, v_fileName_5013_, v_val_4985_, v_traces_5041_, v___x_5042_);
                    leanh::lean_dec_ref(v_traces_5041_);
                    v___x_5044_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_5043_);
                    v___x_5045_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v___x_5045_, 0, v___x_4986_);
                    leanh::lean_ctor_set(v___x_5045_, 1, v___x_5044_);
                    leanh::lean_ctor_set(v___x_5045_, 2, v___x_4987_);
                    leanh::lean_ctor_set(v___x_5045_, 3, v___x_4979_);
                    leanh::lean_ctor_set_uint8(
                        v___x_5045_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v_val_4985_,
                    );
                    v___x_5046_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5046_, 0, v___x_5045_);
                    leanh::lean_ctor_set(v___x_5046_, 1, v___x_5007_);
                    v___x_5047_ = lean_task_pure(v___x_5046_);
                    return v___x_5047_;
                } else {
                    leanh::lean_dec_ref_known(v___x_5038_, 1);
                    leanh::lean_dec(v___x_5009_);
                    leanh::lean_dec(v___x_4987_);
                    leanh::lean_dec_ref(v___x_4986_);
                    leanh::lean_dec_ref(v___x_4979_);
                    v___x_5048_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5048_, 0, v___x_4988_);
                    leanh::lean_ctor_set(v___x_5048_, 1, v___x_5007_);
                    v___x_5049_ = lean_task_pure(v___x_5048_);
                    return v___x_5049_;
                }
            }
            2 => {
                if v___y_5051_ == 0 {
                    v___x_5052_ = lean_st_ref_take(v___x_5009_);
                    v_env_5053_ = leanh::lean_ctor_get(v___x_5052_, 0);
                    v_nextMacroScope_5054_ = leanh::lean_ctor_get(v___x_5052_, 1);
                    v_ngen_5055_ = leanh::lean_ctor_get(v___x_5052_, 2);
                    v_auxDeclNGen_5056_ = leanh::lean_ctor_get(v___x_5052_, 3);
                    v_traceState_5057_ = leanh::lean_ctor_get(v___x_5052_, 4);
                    v_messages_5058_ = leanh::lean_ctor_get(v___x_5052_, 6);
                    v_infoState_5059_ = leanh::lean_ctor_get(v___x_5052_, 7);
                    v_snapshotTasks_5060_ = leanh::lean_ctor_get(v___x_5052_, 8);
                    v_isSharedCheck_5069_ = (!leanh::lean_is_exclusive(v___x_5052_)) as u8;
                    if v_isSharedCheck_5069_ == 0 {
                        v_unused_5070_ = leanh::lean_ctor_get(v___x_5052_, 5);
                        leanh::lean_dec(v_unused_5070_);
                        v___x_5062_ = v___x_5052_;
                        v_isShared_5063_ = v_isSharedCheck_5069_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_5060_);
                        leanh::lean_inc(v_infoState_5059_);
                        leanh::lean_inc(v_messages_5058_);
                        leanh::lean_inc(v_traceState_5057_);
                        leanh::lean_inc(v_auxDeclNGen_5056_);
                        leanh::lean_inc(v_ngen_5055_);
                        leanh::lean_inc(v_nextMacroScope_5054_);
                        leanh::lean_inc(v_env_5053_);
                        leanh::lean_dec(v___x_5052_);
                        v___x_5062_ = leanh::lean_box(0);
                        v_isShared_5063_ = v_isSharedCheck_5069_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v___x_5009_);
                    leanh::lean_inc(v___x_4973_);
                    leanh::lean_inc(v___x_4975_);
                    leanh::lean_inc_ref(v_fileMap_5014_);
                    leanh::lean_inc_ref(v_fileName_5013_);
                    v_fileName_5021_ = v_fileName_5013_;
                    v_fileMap_5022_ = v_fileMap_5014_;
                    v_currRecDepth_5023_ = v___x_4975_;
                    v_ref_5024_ = v___x_5016_;
                    v_currNamespace_5025_ = v___x_4973_;
                    v_openDecls_5026_ = v___x_4997_;
                    v_initHeartbeats_5027_ = v___x_4975_;
                    v_maxHeartbeats_5028_ = v___x_5017_;
                    v_quotContext_5029_ = v___x_4973_;
                    v_currMacroScope_5030_ = v___x_4993_;
                    v_cancelTk_x3f_5031_ = v___x_4989_;
                    v_suppressElabErrors_5032_ = v_val_4985_;
                    v_inheritedTraceOptions_5033_ = v___x_5010_;
                    v___y_5034_ = v___x_5009_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5064_ = l_Lean_Kernel_enableDiag(v_env_5053_, v___x_5019_);
                if v_isShared_5063_ == 0 {
                    leanh::lean_ctor_set(v___x_5062_, 5, v___x_5000_);
                    leanh::lean_ctor_set(v___x_5062_, 0, v___x_5064_);
                    v___x_5066_ = v___x_5062_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5068_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 0, v___x_5064_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 1, v_nextMacroScope_5054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 2, v_ngen_5055_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 3, v_auxDeclNGen_5056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 4, v_traceState_5057_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 5, v___x_5000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 6, v_messages_5058_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 7, v_infoState_5059_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 8, v_snapshotTasks_5060_);
                    v___x_5066_ = v_reuseFailAlloc_5068_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5067_ = lean_st_ref_set(v___x_5009_, v___x_5066_);
                leanh::lean_inc(v___x_5009_);
                leanh::lean_inc(v___x_4973_);
                leanh::lean_inc(v___x_4975_);
                leanh::lean_inc_ref(v_fileMap_5014_);
                leanh::lean_inc_ref(v_fileName_5013_);
                v_fileName_5021_ = v_fileName_5013_;
                v_fileMap_5022_ = v_fileMap_5014_;
                v_currRecDepth_5023_ = v___x_4975_;
                v_ref_5024_ = v___x_5016_;
                v_currNamespace_5025_ = v___x_4973_;
                v_openDecls_5026_ = v___x_4997_;
                v_initHeartbeats_5027_ = v___x_4975_;
                v_maxHeartbeats_5028_ = v___x_5017_;
                v_quotContext_5029_ = v___x_4973_;
                v_currMacroScope_5030_ = v___x_4993_;
                v_cancelTk_x3f_5031_ = v___x_4989_;
                v_suppressElabErrors_5032_ = v_val_4985_;
                v_inheritedTraceOptions_5033_ = v___x_5010_;
                v___y_5034_ = v___x_5009_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5072_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_5073_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_5074_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_5075_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_5076_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_env_5077_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_5078_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_5079_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_5080_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_opts_5081_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_5082_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_pos_5083_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_val_5084_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___x_5085_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___x_5086_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___x_5087_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___x_5088_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___x_5089_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_x_5090_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_5091_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___x_44935__boxed_5092_: usize = 0;
    let mut v___x_44936__boxed_5093_: u8 = 0;
    let mut v_val_44940__boxed_5094_: u8 = 0;
    let mut v___x_44945__boxed_5095_: u8 = 0;
    let mut v_res_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_44935__boxed_5092_ = leanh::lean_unbox_usize(v___x_5075_);
    leanh::lean_dec(v___x_5075_);
    v___x_44936__boxed_5093_ = (leanh::lean_unbox(v___x_5076_) as u8);
    v_val_44940__boxed_5094_ = (leanh::lean_unbox(v_val_5084_) as u8);
    v___x_44945__boxed_5095_ = (leanh::lean_unbox(v___x_5089_) as u8);
    v_res_5096_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(
        v___x_5072_,
        v___x_5073_,
        v___x_5074_,
        v___x_44935__boxed_5092_,
        v___x_44936__boxed_5093_,
        v_env_5077_,
        v___x_5078_,
        v___x_5079_,
        v_a_5080_,
        v_opts_5081_,
        v___x_5082_,
        v_pos_5083_,
        v_val_44940__boxed_5094_,
        v___x_5085_,
        v___x_5086_,
        v___x_5087_,
        v___x_5088_,
        v___x_44945__boxed_5095_,
        v_x_5090_,
    );
    leanh::lean_dec(v_pos_5083_);
    leanh::lean_dec_ref(v_a_5080_);
    leanh::lean_dec(v___x_5079_);
    leanh::lean_dec(v___x_5073_);
    return v_res_5096_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5102_ =
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2;
    v___x_5103_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1;
    v___x_5104_ = l_Lean_Name_append(v___x_5103_, v___x_5102_);
    return v___x_5104_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(
    mut v___x_5105_: *mut leanh::LeanObject,
    mut v___x_5106_: *mut leanh::LeanObject,
    mut v_val_5107_: u8,
    mut v_val_5108_: *mut leanh::LeanObject,
    mut v_val_5109_: *mut leanh::LeanObject,
    mut v___x_5110_: *mut leanh::LeanObject,
    mut v___x_5111_: *mut leanh::LeanObject,
    mut v___x_5112_: u8,
    mut v_a_5113_: *mut leanh::LeanObject,
    mut v_pos_5114_: *mut leanh::LeanObject,
    mut v_infoSt_5115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgLog_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5131_: u8 = 0;
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: u8 = 0;
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: f64 = 0.0;
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcessingContext_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: u8 = 0;
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: u8 = 0;
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_trees_5157_ = leanh::lean_ctor_get(v_infoSt_5115_, 2);
                v_size_5158_ = leanh::lean_ctor_get(v_trees_5157_, 2);
                v___x_5159_ = l_Lean_Elab_instInhabitedInfoTree_default;
                v___x_5160_ = lean_nat_dec_lt(v___x_5111_, v_size_5158_);
                if v___x_5160_ == 0 {
                    v___x_5161_ = l_outOfBounds___redArg(v___x_5159_);
                    v___y_5125_ = v___x_5161_;
                    state = 2;
                    continue;
                } else {
                    v___x_5162_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_5159_,
                        v_trees_5157_,
                        v___x_5111_,
                    );
                    v___y_5125_ = v___x_5162_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5120_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_5119_);
                v___x_5121_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5121_, 0, v___y_5118_);
                v___x_5122_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_5122_, 0, v___x_5105_);
                leanh::lean_ctor_set(v___x_5122_, 1, v___x_5120_);
                leanh::lean_ctor_set(v___x_5122_, 2, v___x_5121_);
                leanh::lean_ctor_set(v___x_5122_, 3, v___x_5106_);
                leanh::lean_ctor_set_uint8(
                    v___x_5122_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v_val_5107_,
                );
                v___x_5123_ = lean_io_promise_resolve(v___x_5122_, v_val_5108_);
                return v___x_5123_;
            }
            2 => {
                v___x_5126_ = l_Lean_inheritedTraceOptions;
                v___x_5127_ = lean_st_ref_get(v___x_5126_);
                v_scopes_5128_ = leanh::lean_ctor_get(v_val_5109_, 2);
                v___x_5129_ = l_List_head_x21___redArg(v___x_5110_, v_scopes_5128_);
                v_opts_5130_ = leanh::lean_ctor_get(v___x_5129_, 1);
                leanh::lean_inc_ref(v_opts_5130_);
                leanh::lean_dec(v___x_5129_);
                v_hasTrace_5131_ = leanh::lean_ctor_get_uint8(
                    v_opts_5130_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_5132_ = l_Lean_MessageLog_empty;
                if v_hasTrace_5131_ == 0 {
                    leanh::lean_dec_ref(v_opts_5130_);
                    leanh::lean_dec(v___x_5127_);
                    leanh::lean_dec(v___x_5111_);
                    v___y_5118_ = v___y_5125_;
                    v_msgLog_5119_ = v___x_5132_;
                    state = 1;
                    continue;
                } else {
                    v___x_5133_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2;
                    v___x_5134_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1;
                    v___x_5135_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3);
                    v___x_5136_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v___x_5127_,
                        v_opts_5130_,
                        v___x_5135_,
                    );
                    leanh::lean_dec_ref(v_opts_5130_);
                    leanh::lean_dec(v___x_5127_);
                    if v___x_5136_ == 0 {
                        leanh::lean_dec(v___x_5111_);
                        v___y_5118_ = v___y_5125_;
                        v_msgLog_5119_ = v___x_5132_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5137_ = leanh::lean_box(0);
                        leanh::lean_inc_ref(v___y_5125_);
                        v___x_5138_ = l_Lean_Elab_InfoTree_format(v___y_5125_, v___x_5137_);
                        if leanh::lean_obj_tag(v___x_5138_) == 0 {
                            v_a_5139_ = leanh::lean_ctor_get(v___x_5138_, 0);
                            leanh::lean_inc(v_a_5139_);
                            leanh::lean_dec_ref_known(v___x_5138_, 1);
                            v___x_5140_ = lean_float_of_nat(v___x_5111_);
                            v___x_5141_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0;
                            v___x_5142_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                            leanh::lean_ctor_set(v___x_5142_, 0, v___x_5133_);
                            leanh::lean_ctor_set(v___x_5142_, 1, v___x_5137_);
                            leanh::lean_ctor_set(v___x_5142_, 2, v___x_5141_);
                            leanh::lean_ctor_set_float(
                                v___x_5142_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                                v___x_5140_,
                            );
                            leanh::lean_ctor_set_float(
                                v___x_5142_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                    as u32,
                                v___x_5140_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_5142_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16)
                                    as u32,
                                v___x_5112_,
                            );
                            v_toProcessingContext_5143_ = leanh::lean_ctor_get(v_a_5113_, 0);
                            v_fileName_5144_ =
                                leanh::lean_ctor_get(v_toProcessingContext_5143_, 1);
                            v_fileMap_5145_ =
                                leanh::lean_ctor_get(v_toProcessingContext_5143_, 2);
                            v___x_5146_ = l_Lean_MessageData_nil;
                            v___x_5147_ = l_Lean_MessageData_ofFormat(v_a_5139_);
                            v___x_5148_ = leanh::lean_unsigned_to_nat(1);
                            v___x_5149_ = lean_mk_empty_array_with_capacity(v___x_5148_);
                            v___x_5150_ = lean_array_push(v___x_5149_, v___x_5147_);
                            v___x_5151_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_5151_, 0, v___x_5142_);
                            leanh::lean_ctor_set(v___x_5151_, 1, v___x_5146_);
                            leanh::lean_ctor_set(v___x_5151_, 2, v___x_5150_);
                            v___x_5152_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5152_, 0, v___x_5134_);
                            leanh::lean_ctor_set(v___x_5152_, 1, v___x_5151_);
                            leanh::lean_inc_ref(v_fileMap_5145_);
                            v___x_5153_ = l_Lean_FileMap_toPosition(v_fileMap_5145_, v_pos_5114_);
                            v___x_5154_ = 0;
                            leanh::lean_inc_ref(v_fileName_5144_);
                            v___x_5155_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                            leanh::lean_ctor_set(v___x_5155_, 0, v_fileName_5144_);
                            leanh::lean_ctor_set(v___x_5155_, 1, v___x_5153_);
                            leanh::lean_ctor_set(v___x_5155_, 2, v___x_5137_);
                            leanh::lean_ctor_set(v___x_5155_, 3, v___x_5141_);
                            leanh::lean_ctor_set(v___x_5155_, 4, v___x_5152_);
                            leanh::lean_ctor_set_uint8(
                                v___x_5155_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                                v_val_5107_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_5155_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1)
                                    as u32,
                                v___x_5154_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_5155_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2)
                                    as u32,
                                v_val_5107_,
                            );
                            v___x_5156_ = l_Lean_MessageLog_add(v___x_5155_, v___x_5132_);
                            v___y_5118_ = v___y_5125_;
                            v_msgLog_5119_ = v___x_5156_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v___x_5138_, 1);
                            leanh::lean_dec(v___x_5111_);
                            v___y_5118_ = v___y_5125_;
                            v_msgLog_5119_ = v___x_5132_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed(
    mut v___x_5163_: *mut leanh::LeanObject,
    mut v___x_5164_: *mut leanh::LeanObject,
    mut v_val_5165_: *mut leanh::LeanObject,
    mut v_val_5166_: *mut leanh::LeanObject,
    mut v_val_5167_: *mut leanh::LeanObject,
    mut v___x_5168_: *mut leanh::LeanObject,
    mut v___x_5169_: *mut leanh::LeanObject,
    mut v___x_5170_: *mut leanh::LeanObject,
    mut v_a_5171_: *mut leanh::LeanObject,
    mut v_pos_5172_: *mut leanh::LeanObject,
    mut v_infoSt_5173_: *mut leanh::LeanObject,
    mut v___y_5174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_45122__boxed_5175_: u8 = 0;
    let mut v___x_45127__boxed_5176_: u8 = 0;
    let mut v_res_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_45122__boxed_5175_ = (leanh::lean_unbox(v_val_5165_) as u8);
    v___x_45127__boxed_5176_ = (leanh::lean_unbox(v___x_5170_) as u8);
    v_res_5177_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(
        v___x_5163_,
        v___x_5164_,
        v_val_45122__boxed_5175_,
        v_val_5166_,
        v_val_5167_,
        v___x_5168_,
        v___x_5169_,
        v___x_45127__boxed_5176_,
        v_a_5171_,
        v_pos_5172_,
        v_infoSt_5173_,
    );
    leanh::lean_dec_ref(v_infoSt_5173_);
    leanh::lean_dec(v_pos_5172_);
    leanh::lean_dec_ref(v_a_5171_);
    leanh::lean_dec_ref(v___x_5168_);
    leanh::lean_dec_ref(v_val_5167_);
    leanh::lean_dec(v_val_5166_);
    return v_res_5177_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(
    mut v_as_5179_: *mut leanh::LeanObject,
    mut v_i_5180_: usize,
    mut v_stop_5181_: usize,
    mut v_b_5182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5184_: u8 = 0;
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: usize = 0;
    let mut v___x_5189_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5184_ = lean_usize_dec_eq(v_i_5180_, v_stop_5181_);
                if v___x_5184_ == 0 {
                    v___x_5185_ = lean_array_uget_borrowed(v_as_5179_, v_i_5180_);
                    v___f_5186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0;
                    leanh::lean_inc(v___x_5185_);
                    v___x_5187_ =
                        l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_5186_, v___x_5185_);
                    v___x_5188_ = 1usize;
                    v___x_5189_ = lean_usize_add(v_i_5180_, v___x_5188_);
                    v_i_5180_ = v___x_5189_;
                    v_b_5182_ = v___x_5187_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5182_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___boxed(
    mut v_as_5191_: *mut leanh::LeanObject,
    mut v_i_5192_: *mut leanh::LeanObject,
    mut v_stop_5193_: *mut leanh::LeanObject,
    mut v_b_5194_: *mut leanh::LeanObject,
    mut v___y_5195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5196_: usize = 0;
    let mut v_stop_boxed_5197_: usize = 0;
    let mut v_res_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5196_ = leanh::lean_unbox_usize(v_i_5192_);
    leanh::lean_dec(v_i_5192_);
    v_stop_boxed_5197_ = leanh::lean_unbox_usize(v_stop_5193_);
    leanh::lean_dec(v_stop_5193_);
    v_res_5198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_5191_, v_i_boxed_5196_, v_stop_boxed_5197_, v_b_5194_);
    leanh::lean_dec_ref(v_as_5191_);
    return v_res_5198_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed(
    mut v_oldResult_5199_: *mut leanh::LeanObject,
    mut v_newParserState_5200_: *mut leanh::LeanObject,
    mut v_val_5201_: *mut leanh::LeanObject,
    mut v_sync_5202_: *mut leanh::LeanObject,
    mut v_val_5203_: *mut leanh::LeanObject,
    mut v_a_5204_: *mut leanh::LeanObject,
    mut v_oldNext_5205_: *mut leanh::LeanObject,
    mut v___y_5206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sync_boxed_5207_: u8 = 0;
    let mut v_res_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5207_ = (leanh::lean_unbox(v_sync_5202_) as u8);
    v_res_5208_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(
        v_oldResult_5199_,
        v_newParserState_5200_,
        v_val_5201_,
        v_sync_boxed_5207_,
        v_val_5203_,
        v_a_5204_,
        v_oldNext_5205_,
    );
    leanh::lean_dec_ref(v_a_5204_);
    return v_res_5208_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(
    mut v_val_5209_: *mut leanh::LeanObject,
    mut v_newParserState_5210_: *mut leanh::LeanObject,
    mut v_val_5211_: *mut leanh::LeanObject,
    mut v_sync_5212_: u8,
    mut v_val_5213_: *mut leanh::LeanObject,
    mut v_a_5214_: *mut leanh::LeanObject,
    mut v_oldResult_5215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_task_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: u8 = 0;
    let mut v___x_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_task_5217_ = leanh::lean_ctor_get(v_val_5209_, 3);
    leanh::lean_inc_ref(v_task_5217_);
    leanh::lean_dec_ref(v_val_5209_);
    v___x_5218_ = leanh::lean_box((v_sync_5212_) as usize);
    leanh::lean_inc_ref(v_a_5214_);
    v___f_5219_ = leanh::lean_alloc_closure(
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed
            as *mut core::ffi::c_void,
        8,
        6,
    );
    leanh::lean_closure_set(v___f_5219_, 0, v_oldResult_5215_);
    leanh::lean_closure_set(v___f_5219_, 1, v_newParserState_5210_);
    leanh::lean_closure_set(v___f_5219_, 2, v_val_5211_);
    leanh::lean_closure_set(v___f_5219_, 3, v___x_5218_);
    leanh::lean_closure_set(v___f_5219_, 4, v_val_5213_);
    leanh::lean_closure_set(v___f_5219_, 5, v_a_5214_);
    v___x_5220_ = leanh::lean_unsigned_to_nat(0);
    v___x_5221_ = 1;
    v___x_5222_ = l_BaseIO_chainTask___redArg(v_task_5217_, v___f_5219_, v___x_5220_, v___x_5221_);
    return v___x_5222_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(
    mut v_val_5223_: *mut leanh::LeanObject,
    mut v_newParserState_5224_: *mut leanh::LeanObject,
    mut v_val_5225_: *mut leanh::LeanObject,
    mut v_sync_5226_: *mut leanh::LeanObject,
    mut v_val_5227_: *mut leanh::LeanObject,
    mut v_a_5228_: *mut leanh::LeanObject,
    mut v_oldResult_5229_: *mut leanh::LeanObject,
    mut v___y_5230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sync_boxed_5231_: u8 = 0;
    let mut v_res_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5231_ = (leanh::lean_unbox(v_sync_5226_) as u8);
    v_res_5232_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(
        v_val_5223_,
        v_newParserState_5224_,
        v_val_5225_,
        v_sync_boxed_5231_,
        v_val_5227_,
        v_a_5228_,
        v_oldResult_5229_,
    );
    leanh::lean_dec_ref(v_a_5228_);
    return v_res_5232_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5234_ = l_Lean_Language_instInhabitedDynamicSnapshot;
    v___x_5235_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_5234_);
    return v___x_5235_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5236_ = l_Lean_Language_instInhabitedSnapshotTree_default;
    v___x_5237_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_5236_);
    return v___x_5237_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5245_ =
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1;
    v___x_5246_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1;
    v___x_5247_ = l_Lean_Name_append(v___x_5246_, v___x_5245_);
    return v___x_5247_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5248_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5248_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5249_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3);
    v___x_5250_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5250_, 0, v___x_5249_);
    return v___x_5250_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(
    mut v___x_5251_: *mut leanh::LeanObject,
    mut v_val_5252_: *mut leanh::LeanObject,
    mut v_fst_5253_: *mut leanh::LeanObject,
    mut v_val_5254_: u8,
    mut v_a_5255_: *mut leanh::LeanObject,
    mut v_snd_5256_: *mut leanh::LeanObject,
    mut v___x_5257_: *mut leanh::LeanObject,
    mut v___x_5258_: u8,
    mut v_fst_5259_: *mut leanh::LeanObject,
    mut v_val_5260_: *mut leanh::LeanObject,
    mut v_val_5261_: *mut leanh::LeanObject,
    mut v_val_5262_: *mut leanh::LeanObject,
    mut v_snd_5263_: *mut leanh::LeanObject,
    mut v_prom_5264_: *mut leanh::LeanObject,
    mut v___x_5265_: *mut leanh::LeanObject,
    mut v___f_5266_: *mut leanh::LeanObject,
    mut v___f_5267_: *mut leanh::LeanObject,
    mut v___f_5268_: *mut leanh::LeanObject,
    mut v_pos_5269_: *mut leanh::LeanObject,
    mut v_fst_5270_: *mut leanh::LeanObject,
    mut v_cmdState_5271_: *mut leanh::LeanObject,
    mut v_opts_5272_: *mut leanh::LeanObject,
    mut v___x_5273_: *mut leanh::LeanObject,
    mut v_old_x3f_5274_: *mut leanh::LeanObject,
    mut v_parseCancelTk_5275_: *mut leanh::LeanObject,
    mut v_next_x3f_5276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceTask_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5310_: usize = 0;
    let mut v___y_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedCmdState_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5345_: u8 = 0;
    let mut v___x_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: u8 = 0;
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5374_: usize = 0;
    let mut v___y_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedCmdState_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5403_: usize = 0;
    let mut v___y_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5411_: usize = 0;
    let mut v___y_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: u8 = 0;
    let mut v___x_5429_: u8 = 0;
    let mut v_env_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: usize = 0;
    let mut v___x_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5498_: u8 = 0;
    let mut v_elabSnap_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elabSnap_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5506_: u8 = 0;
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcessingContext_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_next_x3f_5276_) == 0 {
                    leanh::lean_dec_ref(v_parseCancelTk_5275_);
                    v___x_5507_ = leanh::lean_box(0);
                    v___y_5454_ = v___x_5507_;
                    state = 6;
                    continue;
                } else {
                    v_toProcessingContext_5508_ = leanh::lean_ctor_get(v_a_5255_, 0);
                    v_val_5509_ = leanh::lean_ctor_get(v_next_x3f_5276_, 0);
                    v_pos_5510_ = leanh::lean_ctor_get(v_fst_5253_, 0);
                    v_endPos_5511_ = leanh::lean_ctor_get(v_toProcessingContext_5508_, 3);
                    v___x_5512_ = leanh::lean_box(0);
                    leanh::lean_inc(v_endPos_5511_);
                    leanh::lean_inc(v_pos_5510_);
                    v___x_5513_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5513_, 0, v_pos_5510_);
                    leanh::lean_ctor_set(v___x_5513_, 1, v_endPos_5511_);
                    v___x_5514_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5514_, 0, v___x_5513_);
                    v___x_5515_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5515_, 0, v_parseCancelTk_5275_);
                    v___x_5516_ = l_IO_Promise_result_x21___redArg(v_val_5509_);
                    v___x_5517_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_5517_, 0, v___x_5512_);
                    leanh::lean_ctor_set(v___x_5517_, 1, v___x_5514_);
                    leanh::lean_ctor_set(v___x_5517_, 2, v___x_5515_);
                    leanh::lean_ctor_set(v___x_5517_, 3, v___x_5516_);
                    v___x_5518_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5518_, 0, v___x_5517_);
                    v___y_5454_ = v___x_5518_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                v___x_5286_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5286_, 0, v___y_5280_);
                leanh::lean_ctor_set(v___x_5286_, 1, v___x_5251_);
                leanh::lean_ctor_set(v___x_5286_, 2, v___y_5279_);
                leanh::lean_ctor_set(v___x_5286_, 3, v_traceTask_5285_);
                v___x_5287_ = lean_array_push(v_snapshotTasks_5284_, v___x_5286_);
                v___x_5288_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5288_, 0, v___y_5282_);
                leanh::lean_ctor_set(v___x_5288_, 1, v___x_5287_);
                v___x_5289_ = lean_io_promise_resolve(v___x_5288_, v_val_5252_);
                if leanh::lean_obj_tag(v_next_x3f_5276_) == 1 {
                    v_val_5290_ = leanh::lean_ctor_get(v_next_x3f_5276_, 0);
                    leanh::lean_inc(v_val_5290_);
                    leanh::lean_dec_ref_known(v_next_x3f_5276_, 1);
                    v___x_5291_ = leanh::lean_box(0);
                    v___x_5292_ =
                        l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(
                            v___x_5291_,
                            v_fst_5253_,
                            v___y_5283_,
                            v_val_5290_,
                            v_val_5254_,
                            v___y_5281_,
                            v_a_5255_,
                        );
                    return v___x_5292_;
                } else {
                    leanh::lean_dec_ref(v___y_5283_);
                    leanh::lean_dec_ref(v___y_5281_);
                    leanh::lean_dec(v_next_x3f_5276_);
                    leanh::lean_dec_ref(v_fst_5253_);
                    v___x_5293_ = leanh::lean_box(0);
                    return v___x_5293_;
                }
            }
            2 => {
                v_snapshotTasks_5301_ = leanh::lean_ctor_get(v___y_5300_, 10);
                leanh::lean_inc_ref(v_snapshotTasks_5301_);
                v___x_5302_ = lean_mk_empty_array_with_capacity(v___y_5297_);
                leanh::lean_dec(v___y_5297_);
                leanh::lean_inc_ref(v___y_5299_);
                v___x_5303_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5303_, 0, v___y_5299_);
                leanh::lean_ctor_set(v___x_5303_, 1, v___x_5302_);
                v___x_5304_ = lean_task_pure(v___x_5303_);
                v___y_5279_ = v___y_5296_;
                v___y_5280_ = v___y_5295_;
                v___y_5281_ = v___y_5298_;
                v___y_5282_ = v___y_5299_;
                v___y_5283_ = v___y_5300_;
                v_snapshotTasks_5284_ = v_snapshotTasks_5301_;
                v_traceTask_5285_ = v___x_5304_;
                state = 1;
                continue;
            }
            3 => {
                v___x_5335_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_5328_);
                v___x_5336_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_5336_, 0, v___y_5320_);
                leanh::lean_ctor_set(v___x_5336_, 1, v___x_5335_);
                leanh::lean_ctor_set(v___x_5336_, 2, v___y_5315_);
                leanh::lean_ctor_set(v___x_5336_, 3, v_traceState_5331_);
                leanh::lean_ctor_set_uint8(
                    v___x_5336_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v_val_5254_,
                );
                v___x_5337_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5337_, 0, v___x_5336_);
                leanh::lean_ctor_set(v___x_5337_, 1, v_reportedCmdState_5334_);
                v___x_5338_ = lean_io_promise_resolve(v___x_5337_, v_val_5261_);
                v___x_5339_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_5330_);
                leanh::lean_inc(v___y_5321_);
                v___x_5340_ =
                    l_BaseIO_chainTask___redArg(v___x_5339_, v___y_5316_, v___y_5321_, v___x_5258_);
                v___x_5341_ = l_Lean_inheritedTraceOptions;
                v___x_5342_ = lean_st_ref_get(v___x_5341_);
                v___x_5343_ = l_List_head_x21___redArg(v___x_5265_, v_scopes_5329_);
                leanh::lean_dec(v_scopes_5329_);
                leanh::lean_dec_ref(v___x_5265_);
                v_opts_5344_ = leanh::lean_ctor_get(v___x_5343_, 1);
                leanh::lean_inc_ref(v_opts_5344_);
                leanh::lean_dec(v___x_5343_);
                v_hasTrace_5345_ = leanh::lean_ctor_get_uint8(
                    v_opts_5344_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_5345_ == 0 {
                    leanh::lean_dec_ref(v_opts_5344_);
                    leanh::lean_dec(v___x_5342_);
                    leanh::lean_dec(v___y_5333_);
                    leanh::lean_dec_ref(v_snapshotTasks_5332_);
                    leanh::lean_dec_ref(v_env_5327_);
                    leanh::lean_dec_ref(v___y_5325_);
                    leanh::lean_dec(v___y_5324_);
                    leanh::lean_dec_ref(v___y_5319_);
                    leanh::lean_dec_ref(v___y_5317_);
                    leanh::lean_dec(v___y_5313_);
                    leanh::lean_dec(v___y_5312_);
                    leanh::lean_dec(v___y_5311_);
                    leanh::lean_dec_ref(v___y_5309_);
                    leanh::lean_dec(v___y_5308_);
                    leanh::lean_dec_ref(v___y_5307_);
                    leanh::lean_dec(v_pos_5269_);
                    leanh::lean_dec_ref(v___f_5268_);
                    leanh::lean_dec_ref(v___f_5267_);
                    leanh::lean_dec_ref(v___f_5266_);
                    leanh::lean_dec(v___x_5257_);
                    v___y_5295_ = v___y_5318_;
                    v___y_5296_ = v___y_5314_;
                    v___y_5297_ = v___y_5321_;
                    v___y_5298_ = v___y_5322_;
                    v___y_5299_ = v___y_5323_;
                    v___y_5300_ = v___y_5326_;
                    state = 2;
                    continue;
                } else {
                    v___x_5346_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
                    v___x_5347_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v___x_5342_,
                        v_opts_5344_,
                        v___x_5346_,
                    );
                    leanh::lean_dec(v___x_5342_);
                    if v___x_5347_ == 0 {
                        leanh::lean_dec_ref(v_opts_5344_);
                        leanh::lean_dec(v___y_5333_);
                        leanh::lean_dec_ref(v_snapshotTasks_5332_);
                        leanh::lean_dec_ref(v_env_5327_);
                        leanh::lean_dec_ref(v___y_5325_);
                        leanh::lean_dec(v___y_5324_);
                        leanh::lean_dec_ref(v___y_5319_);
                        leanh::lean_dec_ref(v___y_5317_);
                        leanh::lean_dec(v___y_5313_);
                        leanh::lean_dec(v___y_5312_);
                        leanh::lean_dec(v___y_5311_);
                        leanh::lean_dec_ref(v___y_5309_);
                        leanh::lean_dec(v___y_5308_);
                        leanh::lean_dec_ref(v___y_5307_);
                        leanh::lean_dec(v_pos_5269_);
                        leanh::lean_dec_ref(v___f_5268_);
                        leanh::lean_dec_ref(v___f_5267_);
                        leanh::lean_dec_ref(v___f_5266_);
                        leanh::lean_dec(v___x_5257_);
                        v___y_5295_ = v___y_5318_;
                        v___y_5296_ = v___y_5314_;
                        v___y_5297_ = v___y_5321_;
                        v___y_5298_ = v___y_5322_;
                        v___y_5299_ = v___y_5323_;
                        v___y_5300_ = v___y_5326_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc_n(v___y_5321_, 3);
                        v___x_5348_ =
                            lean_task_map(v___f_5266_, v___y_5317_, v___y_5321_, v___x_5258_);
                        leanh::lean_inc_n(v___y_5314_, 3);
                        leanh::lean_inc_n(v___y_5333_, 2);
                        leanh::lean_inc_n(v___y_5324_, 2);
                        v___x_5349_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_5349_, 0, v___y_5324_);
                        leanh::lean_ctor_set(v___x_5349_, 1, v___y_5333_);
                        leanh::lean_ctor_set(v___x_5349_, 2, v___y_5314_);
                        leanh::lean_ctor_set(v___x_5349_, 3, v___x_5348_);
                        v___x_5350_ =
                            lean_task_map(v___f_5267_, v___y_5319_, v___y_5321_, v___x_5258_);
                        v___x_5351_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_5351_, 0, v___y_5324_);
                        leanh::lean_ctor_set(v___x_5351_, 1, v___y_5333_);
                        leanh::lean_ctor_set(v___x_5351_, 2, v___y_5314_);
                        leanh::lean_ctor_set(v___x_5351_, 3, v___x_5350_);
                        v___x_5352_ =
                            lean_task_map(v___f_5268_, v___y_5325_, v___y_5321_, v___x_5258_);
                        v___x_5353_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_5353_, 0, v___y_5324_);
                        leanh::lean_ctor_set(v___x_5353_, 1, v___y_5333_);
                        leanh::lean_ctor_set(v___x_5353_, 2, v___y_5314_);
                        leanh::lean_ctor_set(v___x_5353_, 3, v___x_5352_);
                        v___x_5354_ = leanh::lean_unsigned_to_nat(3);
                        v___x_5355_ = lean_mk_empty_array_with_capacity(v___x_5354_);
                        v___x_5356_ = lean_array_push(v___x_5355_, v___x_5349_);
                        v___x_5357_ = lean_array_push(v___x_5356_, v___x_5351_);
                        v___x_5358_ = lean_array_push(v___x_5357_, v___x_5353_);
                        v___x_5359_ = l_Array_append___redArg(v___x_5358_, v_snapshotTasks_5332_);
                        leanh::lean_inc_ref(v___y_5323_);
                        v___x_5360_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5360_, 0, v___y_5323_);
                        leanh::lean_ctor_set(v___x_5360_, 1, v___x_5359_);
                        leanh::lean_inc_ref(v___x_5360_);
                        v___x_5361_ = l_Lean_Language_SnapshotTree_waitAll(v___x_5360_);
                        v___x_5362_ = leanh::lean_box_usize(v___y_5310_);
                        v___x_5363_ = leanh::lean_box((v___x_5258_) as usize);
                        v___x_5364_ = leanh::lean_box((v_val_5254_) as usize);
                        v___x_5365_ = leanh::lean_box((v___x_5347_) as usize);
                        leanh::lean_inc_ref(v_a_5255_);
                        leanh::lean_inc_ref(v___y_5306_);
                        v___f_5366_ = leanh::lean_alloc_closure(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed as *mut core::ffi::c_void, 20, 18);
                        leanh::lean_closure_set(v___f_5366_, 0, v___x_5257_);
                        leanh::lean_closure_set(v___f_5366_, 1, v___y_5312_);
                        leanh::lean_closure_set(v___f_5366_, 2, v___y_5311_);
                        leanh::lean_closure_set(v___f_5366_, 3, v___x_5362_);
                        leanh::lean_closure_set(v___f_5366_, 4, v___x_5363_);
                        leanh::lean_closure_set(v___f_5366_, 5, v_env_5327_);
                        leanh::lean_closure_set(v___f_5366_, 6, v___y_5306_);
                        leanh::lean_closure_set(v___f_5366_, 7, v___x_5341_);
                        leanh::lean_closure_set(v___f_5366_, 8, v_a_5255_);
                        leanh::lean_closure_set(v___f_5366_, 9, v_opts_5344_);
                        leanh::lean_closure_set(v___f_5366_, 10, v___x_5360_);
                        leanh::lean_closure_set(v___f_5366_, 11, v_pos_5269_);
                        leanh::lean_closure_set(v___f_5366_, 12, v___x_5364_);
                        leanh::lean_closure_set(v___f_5366_, 13, v___y_5309_);
                        leanh::lean_closure_set(v___f_5366_, 14, v___y_5313_);
                        leanh::lean_closure_set(v___f_5366_, 15, v___y_5307_);
                        leanh::lean_closure_set(v___f_5366_, 16, v___y_5308_);
                        leanh::lean_closure_set(v___f_5366_, 17, v___x_5365_);
                        v___x_5367_ =
                            lean_io_bind_task(v___x_5361_, v___f_5366_, v___y_5321_, v_val_5254_);
                        v___y_5279_ = v___y_5314_;
                        v___y_5280_ = v___y_5318_;
                        v___y_5281_ = v___y_5322_;
                        v___y_5282_ = v___y_5323_;
                        v___y_5283_ = v___y_5326_;
                        v_snapshotTasks_5284_ = v_snapshotTasks_5332_;
                        v_traceTask_5285_ = v___x_5367_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                v_env_5392_ = leanh::lean_ctor_get(v___y_5389_, 0);
                leanh::lean_inc_ref(v_env_5392_);
                v_messages_5393_ = leanh::lean_ctor_get(v___y_5389_, 1);
                leanh::lean_inc_ref(v_messages_5393_);
                v_scopes_5394_ = leanh::lean_ctor_get(v___y_5389_, 2);
                leanh::lean_inc(v_scopes_5394_);
                v_infoState_5395_ = leanh::lean_ctor_get(v___y_5389_, 8);
                leanh::lean_inc_ref(v_infoState_5395_);
                v_traceState_5396_ = leanh::lean_ctor_get(v___y_5389_, 9);
                leanh::lean_inc_ref(v_traceState_5396_);
                v_snapshotTasks_5397_ = leanh::lean_ctor_get(v___y_5389_, 10);
                leanh::lean_inc_ref(v_snapshotTasks_5397_);
                v___y_5306_ = v___y_5369_;
                v___y_5307_ = v___y_5370_;
                v___y_5308_ = v___y_5371_;
                v___y_5309_ = v___y_5372_;
                v___y_5310_ = v___y_5374_;
                v___y_5311_ = v___y_5373_;
                v___y_5312_ = v___y_5375_;
                v___y_5313_ = v___y_5376_;
                v___y_5314_ = v___y_5377_;
                v___y_5315_ = v___y_5378_;
                v___y_5316_ = v___y_5379_;
                v___y_5317_ = v___y_5380_;
                v___y_5318_ = v___y_5381_;
                v___y_5319_ = v___y_5382_;
                v___y_5320_ = v___y_5383_;
                v___y_5321_ = v___y_5384_;
                v___y_5322_ = v___y_5385_;
                v___y_5323_ = v___y_5386_;
                v___y_5324_ = v___y_5387_;
                v___y_5325_ = v___y_5388_;
                v___y_5326_ = v___y_5389_;
                v_env_5327_ = v_env_5392_;
                v_messages_5328_ = v_messages_5393_;
                v_scopes_5329_ = v_scopes_5394_;
                v_infoState_5330_ = v_infoState_5395_;
                v_traceState_5331_ = v_traceState_5396_;
                v_snapshotTasks_5332_ = v_snapshotTasks_5397_;
                v___y_5333_ = v___y_5390_;
                v_reportedCmdState_5334_ = v_reportedCmdState_5391_;
                state = 3;
                continue;
            }
            5 => {
                v___x_5423_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5423_, 0, v___y_5422_);
                leanh::lean_ctor_set(v___x_5423_, 1, v_val_5260_);
                leanh::lean_inc_ref(v___y_5417_);
                leanh::lean_inc_n(v_pos_5269_, 2);
                leanh::lean_inc(v_fst_5270_);
                v___x_5424_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(
                    v_fst_5270_,
                    v_cmdState_5271_,
                    v_pos_5269_,
                    v___x_5423_,
                    v___y_5417_,
                    v_a_5255_,
                );
                v___x_5425_ = leanh::lean_box((v_val_5254_) as usize);
                v___x_5426_ = leanh::lean_box((v___x_5258_) as usize);
                leanh::lean_inc_ref(v_a_5255_);
                leanh::lean_inc(v___y_5404_);
                leanh::lean_inc_ref(v___x_5265_);
                leanh::lean_inc_ref(v___x_5424_);
                leanh::lean_inc_ref(v___y_5399_);
                leanh::lean_inc_ref(v___y_5402_);
                v___f_5427_ = leanh::lean_alloc_closure(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed as *mut core::ffi::c_void, 12, 10);
                leanh::lean_closure_set(v___f_5427_, 0, v___y_5402_);
                leanh::lean_closure_set(v___f_5427_, 1, v___y_5399_);
                leanh::lean_closure_set(v___f_5427_, 2, v___x_5425_);
                leanh::lean_closure_set(v___f_5427_, 3, v_val_5262_);
                leanh::lean_closure_set(v___f_5427_, 4, v___x_5424_);
                leanh::lean_closure_set(v___f_5427_, 5, v___x_5265_);
                leanh::lean_closure_set(v___f_5427_, 6, v___y_5404_);
                leanh::lean_closure_set(v___f_5427_, 7, v___x_5426_);
                leanh::lean_closure_set(v___f_5427_, 8, v_a_5255_);
                leanh::lean_closure_set(v___f_5427_, 9, v_pos_5269_);
                v___x_5428_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_5272_, v___x_5273_);
                if v___x_5428_ == 0 {
                    leanh::lean_dec(v___y_5408_);
                    leanh::lean_dec(v_fst_5270_);
                    leanh::lean_inc_ref(v___x_5424_);
                    v___y_5369_ = v___y_5399_;
                    v___y_5370_ = v___y_5400_;
                    v___y_5371_ = v___y_5401_;
                    v___y_5372_ = v___y_5402_;
                    v___y_5373_ = v___y_5404_;
                    v___y_5374_ = v___y_5403_;
                    v___y_5375_ = v___y_5405_;
                    v___y_5376_ = v___y_5406_;
                    v___y_5377_ = v___y_5407_;
                    v___y_5378_ = v___y_5409_;
                    v___y_5379_ = v___f_5427_;
                    v___y_5380_ = v___y_5412_;
                    v___y_5381_ = v___y_5413_;
                    v___y_5382_ = v___y_5414_;
                    v___y_5383_ = v___y_5415_;
                    v___y_5384_ = v___y_5416_;
                    v___y_5385_ = v___y_5417_;
                    v___y_5386_ = v___y_5418_;
                    v___y_5387_ = v___y_5419_;
                    v___y_5388_ = v___y_5420_;
                    v___y_5389_ = v___x_5424_;
                    v___y_5390_ = v___y_5421_;
                    v_reportedCmdState_5391_ = v___x_5424_;
                    state = 4;
                    continue;
                } else {
                    v___x_5429_ = l_Lean_Parser_isTerminalCommand(v_fst_5270_);
                    if v___x_5429_ == 0 {
                        if v___x_5428_ == 0 {
                            leanh::lean_dec(v___y_5408_);
                            leanh::lean_inc_ref(v___x_5424_);
                            v___y_5369_ = v___y_5399_;
                            v___y_5370_ = v___y_5400_;
                            v___y_5371_ = v___y_5401_;
                            v___y_5372_ = v___y_5402_;
                            v___y_5373_ = v___y_5404_;
                            v___y_5374_ = v___y_5403_;
                            v___y_5375_ = v___y_5405_;
                            v___y_5376_ = v___y_5406_;
                            v___y_5377_ = v___y_5407_;
                            v___y_5378_ = v___y_5409_;
                            v___y_5379_ = v___f_5427_;
                            v___y_5380_ = v___y_5412_;
                            v___y_5381_ = v___y_5413_;
                            v___y_5382_ = v___y_5414_;
                            v___y_5383_ = v___y_5415_;
                            v___y_5384_ = v___y_5416_;
                            v___y_5385_ = v___y_5417_;
                            v___y_5386_ = v___y_5418_;
                            v___y_5387_ = v___y_5419_;
                            v___y_5388_ = v___y_5420_;
                            v___y_5389_ = v___x_5424_;
                            v___y_5390_ = v___y_5421_;
                            v_reportedCmdState_5391_ = v___x_5424_;
                            state = 4;
                            continue;
                        } else {
                            v_env_5430_ = leanh::lean_ctor_get(v___x_5424_, 0);
                            leanh::lean_inc_ref_n(v_env_5430_, 2);
                            v_messages_5431_ = leanh::lean_ctor_get(v___x_5424_, 1);
                            leanh::lean_inc_ref(v_messages_5431_);
                            v_scopes_5432_ = leanh::lean_ctor_get(v___x_5424_, 2);
                            leanh::lean_inc(v_scopes_5432_);
                            v_infoState_5433_ = leanh::lean_ctor_get(v___x_5424_, 8);
                            leanh::lean_inc_ref(v_infoState_5433_);
                            v_traceState_5434_ = leanh::lean_ctor_get(v___x_5424_, 9);
                            leanh::lean_inc_ref(v_traceState_5434_);
                            v_snapshotTasks_5435_ = leanh::lean_ctor_get(v___x_5424_, 10);
                            leanh::lean_inc_ref(v_snapshotTasks_5435_);
                            v___x_5436_ = lean_mk_empty_array_with_capacity(v___y_5408_);
                            leanh::lean_dec(v___y_5408_);
                            leanh::lean_inc_ref(v___x_5436_);
                            v___x_5437_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5437_, 0, v___x_5436_);
                            leanh::lean_inc_n(v___y_5416_, 3);
                            v___x_5438_ = leanh::lean_alloc_ctor(
                                0,
                                4,
                                (core::mem::size_of::<usize>() * 1) as u32,
                            );
                            leanh::lean_ctor_set(v___x_5438_, 0, v___x_5437_);
                            leanh::lean_ctor_set(v___x_5438_, 1, v___x_5436_);
                            leanh::lean_ctor_set(v___x_5438_, 2, v___y_5416_);
                            leanh::lean_ctor_set(v___x_5438_, 3, v___y_5416_);
                            leanh::lean_ctor_set_usize(v___x_5438_, 4, v___y_5411_);
                            v___x_5439_ = l_Lean_NameSet_empty;
                            leanh::lean_inc_ref_n(v___x_5438_, 2);
                            v___x_5440_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_5440_, 0, v___x_5438_);
                            leanh::lean_ctor_set(v___x_5440_, 1, v___x_5438_);
                            leanh::lean_ctor_set(v___x_5440_, 2, v___x_5439_);
                            v___x_5441_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0;
                            v___x_5442_ = l_Lean_Options_empty;
                            v___x_5443_ = leanh::lean_box(0);
                            v___x_5444_ = lean_mk_empty_array_with_capacity(v___y_5416_);
                            leanh::lean_inc_ref_n(v___x_5444_, 2);
                            leanh::lean_inc_n(v___x_5257_, 2);
                            v___x_5445_ = leanh::lean_alloc_ctor(0, 10, (3) as u32);
                            leanh::lean_ctor_set(v___x_5445_, 0, v___x_5441_);
                            leanh::lean_ctor_set(v___x_5445_, 1, v___x_5442_);
                            leanh::lean_ctor_set(v___x_5445_, 2, v___x_5257_);
                            leanh::lean_ctor_set(v___x_5445_, 3, v___x_5443_);
                            leanh::lean_ctor_set(v___x_5445_, 4, v___x_5443_);
                            leanh::lean_ctor_set(v___x_5445_, 5, v___x_5444_);
                            leanh::lean_ctor_set(v___x_5445_, 6, v___x_5444_);
                            leanh::lean_ctor_set(v___x_5445_, 7, v___x_5443_);
                            leanh::lean_ctor_set(v___x_5445_, 8, v___x_5443_);
                            leanh::lean_ctor_set(v___x_5445_, 9, v___x_5443_);
                            leanh::lean_ctor_set_uint8(
                                v___x_5445_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                                v_val_5254_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_5445_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 1)
                                    as u32,
                                v_val_5254_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_5445_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 2)
                                    as u32,
                                v_val_5254_,
                            );
                            v___x_5446_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5446_, 0, v___x_5445_);
                            leanh::lean_ctor_set(v___x_5446_, 1, v___x_5443_);
                            v___x_5447_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
                            v___x_5448_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3;
                            v___x_5449_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_5257_);
                            v___x_5450_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
                            v___x_5451_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                            leanh::lean_ctor_set(v___x_5451_, 0, v___x_5450_);
                            leanh::lean_ctor_set(v___x_5451_, 1, v___x_5450_);
                            leanh::lean_ctor_set(v___x_5451_, 2, v___x_5438_);
                            leanh::lean_ctor_set_uint8(
                                v___x_5451_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                                v___x_5258_,
                            );
                            leanh::lean_inc_ref(v___y_5410_);
                            v___x_5452_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                            leanh::lean_ctor_set(v___x_5452_, 0, v_env_5430_);
                            leanh::lean_ctor_set(v___x_5452_, 1, v___x_5440_);
                            leanh::lean_ctor_set(v___x_5452_, 2, v___x_5446_);
                            leanh::lean_ctor_set(v___x_5452_, 3, v___x_5439_);
                            leanh::lean_ctor_set(v___x_5452_, 4, v___x_5447_);
                            leanh::lean_ctor_set(v___x_5452_, 5, v___y_5416_);
                            leanh::lean_ctor_set(v___x_5452_, 6, v___x_5448_);
                            leanh::lean_ctor_set(v___x_5452_, 7, v___x_5449_);
                            leanh::lean_ctor_set(v___x_5452_, 8, v___x_5451_);
                            leanh::lean_ctor_set(v___x_5452_, 9, v___y_5410_);
                            leanh::lean_ctor_set(v___x_5452_, 10, v___x_5444_);
                            v___y_5306_ = v___y_5399_;
                            v___y_5307_ = v___y_5400_;
                            v___y_5308_ = v___y_5401_;
                            v___y_5309_ = v___y_5402_;
                            v___y_5310_ = v___y_5403_;
                            v___y_5311_ = v___y_5404_;
                            v___y_5312_ = v___y_5405_;
                            v___y_5313_ = v___y_5406_;
                            v___y_5314_ = v___y_5407_;
                            v___y_5315_ = v___y_5409_;
                            v___y_5316_ = v___f_5427_;
                            v___y_5317_ = v___y_5412_;
                            v___y_5318_ = v___y_5413_;
                            v___y_5319_ = v___y_5414_;
                            v___y_5320_ = v___y_5415_;
                            v___y_5321_ = v___y_5416_;
                            v___y_5322_ = v___y_5417_;
                            v___y_5323_ = v___y_5418_;
                            v___y_5324_ = v___y_5419_;
                            v___y_5325_ = v___y_5420_;
                            v___y_5326_ = v___x_5424_;
                            v_env_5327_ = v_env_5430_;
                            v_messages_5328_ = v_messages_5431_;
                            v_scopes_5329_ = v_scopes_5432_;
                            v_infoState_5330_ = v_infoState_5433_;
                            v_traceState_5331_ = v_traceState_5434_;
                            v_snapshotTasks_5332_ = v_snapshotTasks_5435_;
                            v___y_5333_ = v___y_5421_;
                            v_reportedCmdState_5334_ = v___x_5452_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___y_5408_);
                        leanh::lean_inc_ref(v___x_5424_);
                        v___y_5369_ = v___y_5399_;
                        v___y_5370_ = v___y_5400_;
                        v___y_5371_ = v___y_5401_;
                        v___y_5372_ = v___y_5402_;
                        v___y_5373_ = v___y_5404_;
                        v___y_5374_ = v___y_5403_;
                        v___y_5375_ = v___y_5405_;
                        v___y_5376_ = v___y_5406_;
                        v___y_5377_ = v___y_5407_;
                        v___y_5378_ = v___y_5409_;
                        v___y_5379_ = v___f_5427_;
                        v___y_5380_ = v___y_5412_;
                        v___y_5381_ = v___y_5413_;
                        v___y_5382_ = v___y_5414_;
                        v___y_5383_ = v___y_5415_;
                        v___y_5384_ = v___y_5416_;
                        v___y_5385_ = v___y_5417_;
                        v___y_5386_ = v___y_5418_;
                        v___y_5387_ = v___y_5419_;
                        v___y_5388_ = v___y_5420_;
                        v___y_5389_ = v___x_5424_;
                        v___y_5390_ = v___y_5421_;
                        v_reportedCmdState_5391_ = v___x_5424_;
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5455_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_5256_);
                v___x_5456_ = l_IO_CancelToken_new();
                v___x_5457_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0;
                leanh::lean_inc(v___x_5257_);
                v___x_5458_ = l_Lean_Name_str___override(v___x_5257_, v___x_5457_);
                v___x_5459_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2;
                v___x_5460_ = l_Lean_Name_str___override(v___x_5458_, v___x_5459_);
                v___x_5461_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4;
                v___x_5462_ = l_Lean_Name_str___override(v___x_5460_, v___x_5461_);
                v___x_5463_ = l_Lean_Name_str___override(v___x_5462_, v___x_5459_);
                v___x_5464_ = leanh::lean_unsigned_to_nat(0);
                v___x_5465_ = l_Lean_Name_num___override(v___x_5463_, v___x_5464_);
                v___x_5466_ = l_Lean_Name_str___override(v___x_5465_, v___x_5459_);
                v___x_5467_ = l_Lean_Name_str___override(v___x_5466_, v___x_5461_);
                v___x_5468_ = l_Lean_Name_str___override(v___x_5467_, v___x_5459_);
                v___x_5469_ =
                    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0;
                v___x_5470_ = l_Lean_Name_str___override(v___x_5468_, v___x_5469_);
                v___x_5471_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5;
                v___x_5472_ = l_Lean_Name_str___override(v___x_5470_, v___x_5471_);
                v___x_5473_ = l_Lean_Name_toString(v___x_5472_, v___x_5258_);
                v___x_5474_ = leanh::lean_box(0);
                v___x_5475_ = leanh::lean_unsigned_to_nat(32);
                v___x_5476_ = 5usize;
                v___x_5477_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
                leanh::lean_inc_ref_n(v___x_5473_, 2);
                v___x_5478_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_5478_, 0, v___x_5473_);
                leanh::lean_ctor_set(v___x_5478_, 1, v___x_5455_);
                leanh::lean_ctor_set(v___x_5478_, 2, v___x_5474_);
                leanh::lean_ctor_set(v___x_5478_, 3, v___x_5477_);
                leanh::lean_ctor_set_uint8(
                    v___x_5478_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v_val_5254_,
                );
                v___x_5479_ = l_Lean_Language_Snapshot_Diagnostics_empty;
                v___x_5480_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_5480_, 0, v___x_5473_);
                leanh::lean_ctor_set(v___x_5480_, 1, v___x_5479_);
                leanh::lean_ctor_set(v___x_5480_, 2, v___x_5474_);
                leanh::lean_ctor_set(v___x_5480_, 3, v___x_5477_);
                leanh::lean_ctor_set_uint8(
                    v___x_5480_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v_val_5254_,
                );
                leanh::lean_inc(v_fst_5259_);
                v___x_5481_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5481_, 0, v_fst_5259_);
                v___x_5482_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_5481_);
                leanh::lean_inc_ref(v___x_5456_);
                v___x_5483_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5483_, 0, v___x_5456_);
                v___x_5484_ = l_IO_Promise_result_x21___redArg(v_val_5260_);
                leanh::lean_inc_ref(v___x_5484_);
                leanh::lean_inc(v___x_5482_);
                leanh::lean_inc_ref_n(v___x_5481_, 3);
                v___x_5485_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5485_, 0, v___x_5481_);
                leanh::lean_ctor_set(v___x_5485_, 1, v___x_5482_);
                leanh::lean_ctor_set(v___x_5485_, 2, v___x_5483_);
                leanh::lean_ctor_set(v___x_5485_, 3, v___x_5484_);
                v___x_5486_ = l_IO_Promise_result_x21___redArg(v_val_5261_);
                leanh::lean_inc_ref(v___x_5486_);
                leanh::lean_inc_n(v___x_5251_, 3);
                v___x_5487_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5487_, 0, v___x_5481_);
                leanh::lean_ctor_set(v___x_5487_, 1, v___x_5251_);
                leanh::lean_ctor_set(v___x_5487_, 2, v___x_5474_);
                leanh::lean_ctor_set(v___x_5487_, 3, v___x_5486_);
                v___x_5488_ = l_IO_Promise_result_x21___redArg(v_val_5262_);
                leanh::lean_inc_ref(v___x_5488_);
                v___x_5489_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5489_, 0, v___x_5481_);
                leanh::lean_ctor_set(v___x_5489_, 1, v___x_5251_);
                leanh::lean_ctor_set(v___x_5489_, 2, v___x_5474_);
                leanh::lean_ctor_set(v___x_5489_, 3, v___x_5488_);
                v___x_5490_ = l_IO_Promise_result_x21___redArg(v_val_5252_);
                v___x_5491_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5491_, 0, v___x_5474_);
                leanh::lean_ctor_set(v___x_5491_, 1, v___x_5251_);
                leanh::lean_ctor_set(v___x_5491_, 2, v___x_5474_);
                leanh::lean_ctor_set(v___x_5491_, 3, v___x_5490_);
                leanh::lean_inc_ref(v___x_5480_);
                v___x_5492_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5492_, 0, v___x_5480_);
                leanh::lean_ctor_set(v___x_5492_, 1, v___x_5485_);
                leanh::lean_ctor_set(v___x_5492_, 2, v___x_5487_);
                leanh::lean_ctor_set(v___x_5492_, 3, v___x_5489_);
                leanh::lean_ctor_set(v___x_5492_, 4, v___x_5491_);
                v___x_5493_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5493_, 0, v___x_5478_);
                leanh::lean_ctor_set(v___x_5493_, 1, v_fst_5259_);
                leanh::lean_ctor_set(v___x_5493_, 2, v_snd_5263_);
                leanh::lean_ctor_set(v___x_5493_, 3, v___x_5492_);
                leanh::lean_ctor_set(v___x_5493_, 4, v___y_5454_);
                v___x_5494_ = lean_io_promise_resolve(v___x_5493_, v_prom_5264_);
                if leanh::lean_obj_tag(v_old_x3f_5274_) == 0 {
                    leanh::lean_inc_ref(v___x_5473_);
                    leanh::lean_inc_ref(v___x_5480_);
                    v___y_5399_ = v___x_5477_;
                    v___y_5400_ = v___x_5480_;
                    v___y_5401_ = v___x_5474_;
                    v___y_5402_ = v___x_5473_;
                    v___y_5403_ = v___x_5476_;
                    v___y_5404_ = v___x_5464_;
                    v___y_5405_ = v___x_5475_;
                    v___y_5406_ = v___x_5474_;
                    v___y_5407_ = v___x_5474_;
                    v___y_5408_ = v___x_5475_;
                    v___y_5409_ = v___x_5474_;
                    v___y_5410_ = v___x_5477_;
                    v___y_5411_ = v___x_5476_;
                    v___y_5412_ = v___x_5484_;
                    v___y_5413_ = v___x_5474_;
                    v___y_5414_ = v___x_5486_;
                    v___y_5415_ = v___x_5473_;
                    v___y_5416_ = v___x_5464_;
                    v___y_5417_ = v___x_5456_;
                    v___y_5418_ = v___x_5480_;
                    v___y_5419_ = v___x_5481_;
                    v___y_5420_ = v___x_5488_;
                    v___y_5421_ = v___x_5482_;
                    v___y_5422_ = v___x_5474_;
                    state = 5;
                    continue;
                } else {
                    v_val_5495_ = leanh::lean_ctor_get(v_old_x3f_5274_, 0);
                    v_isSharedCheck_5506_ =
                        (!leanh::lean_is_exclusive(v_old_x3f_5274_)) as u8;
                    if v_isSharedCheck_5506_ == 0 {
                        v___x_5497_ = v_old_x3f_5274_;
                        v_isShared_5498_ = v_isSharedCheck_5506_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5495_);
                        leanh::lean_dec(v_old_x3f_5274_);
                        v___x_5497_ = leanh::lean_box(0);
                        v_isShared_5498_ = v_isSharedCheck_5506_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v_elabSnap_5499_ = leanh::lean_ctor_get(v_val_5495_, 3);
                leanh::lean_inc_ref(v_elabSnap_5499_);
                v_stx_5500_ = leanh::lean_ctor_get(v_val_5495_, 1);
                leanh::lean_inc(v_stx_5500_);
                leanh::lean_dec(v_val_5495_);
                v_elabSnap_5501_ = leanh::lean_ctor_get(v_elabSnap_5499_, 1);
                leanh::lean_inc_ref(v_elabSnap_5501_);
                leanh::lean_dec_ref(v_elabSnap_5499_);
                v___x_5502_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5502_, 0, v_stx_5500_);
                leanh::lean_ctor_set(v___x_5502_, 1, v_elabSnap_5501_);
                if v_isShared_5498_ == 0 {
                    leanh::lean_ctor_set(v___x_5497_, 0, v___x_5502_);
                    v___x_5504_ = v___x_5497_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5505_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5502_);
                    v___x_5504_ = v_reuseFailAlloc_5505_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                leanh::lean_inc_ref(v___x_5473_);
                leanh::lean_inc_ref(v___x_5480_);
                v___y_5399_ = v___x_5477_;
                v___y_5400_ = v___x_5480_;
                v___y_5401_ = v___x_5474_;
                v___y_5402_ = v___x_5473_;
                v___y_5403_ = v___x_5476_;
                v___y_5404_ = v___x_5464_;
                v___y_5405_ = v___x_5475_;
                v___y_5406_ = v___x_5474_;
                v___y_5407_ = v___x_5474_;
                v___y_5408_ = v___x_5475_;
                v___y_5409_ = v___x_5474_;
                v___y_5410_ = v___x_5477_;
                v___y_5411_ = v___x_5476_;
                v___y_5412_ = v___x_5484_;
                v___y_5413_ = v___x_5474_;
                v___y_5414_ = v___x_5486_;
                v___y_5415_ = v___x_5473_;
                v___y_5416_ = v___x_5464_;
                v___y_5417_ = v___x_5456_;
                v___y_5418_ = v___x_5480_;
                v___y_5419_ = v___x_5481_;
                v___y_5420_ = v___x_5488_;
                v___y_5421_ = v___x_5482_;
                v___y_5422_ = v___x_5504_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(
    mut v_fst_5519_: *mut leanh::LeanObject,
    mut v_val_5520_: u8,
    mut v_a_5521_: *mut leanh::LeanObject,
    mut v_snd_5522_: *mut leanh::LeanObject,
    mut v___x_5523_: *mut leanh::LeanObject,
    mut v___x_5524_: u8,
    mut v_prom_5525_: *mut leanh::LeanObject,
    mut v___x_5526_: *mut leanh::LeanObject,
    mut v___f_5527_: *mut leanh::LeanObject,
    mut v___f_5528_: *mut leanh::LeanObject,
    mut v___f_5529_: *mut leanh::LeanObject,
    mut v_pos_5530_: *mut leanh::LeanObject,
    mut v_fst_5531_: *mut leanh::LeanObject,
    mut v_cmdState_5532_: *mut leanh::LeanObject,
    mut v_opts_5533_: *mut leanh::LeanObject,
    mut v_old_x3f_5534_: *mut leanh::LeanObject,
    mut v_parseCancelTk_5535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceTask_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5575_: usize = 0;
    let mut v___y_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedCmdState_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5614_: u8 = 0;
    let mut v___x_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: u8 = 0;
    let mut v___x_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5640_: usize = 0;
    let mut v___y_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedCmdState_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5673_: usize = 0;
    let mut v___y_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5688_: usize = 0;
    let mut v___y_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: u8 = 0;
    let mut v___x_5703_: u8 = 0;
    let mut v_env_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: usize = 0;
    let mut v___x_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5777_: u8 = 0;
    let mut v_elabSnap_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elabSnap_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5785_: u8 = 0;
    let mut v___y_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: u8 = 0;
    let mut v___x_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcessingContext_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5813_: u8 = 0;
    let mut v___x_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5818_: u8 = 0;
    let mut v___y_5820_: u8 = 0;
    let mut v___x_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: u8 = 0;
    let mut v___x_5824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5537_ = lean_io_promise_new();
                v___x_5538_ = lean_io_promise_new();
                v___x_5539_ = lean_io_promise_new();
                v___x_5540_ = lean_io_promise_new();
                v___x_5669_ = l_Lean_internal_cmdlineSnapshots;
                v___x_5823_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_5533_, v___x_5669_);
                if v___x_5823_ == 0 {
                    v___y_5820_ = v___x_5823_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_5531_);
                    v___x_5824_ = l_Lean_Parser_isTerminalCommand(v_fst_5531_);
                    if v___x_5824_ == 0 {
                        v___y_5820_ = v___x_5823_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_fst_5519_);
                        leanh::lean_inc(v_fst_5531_);
                        v_fst_5806_ = v_fst_5531_;
                        v_snd_5807_ = v_fst_5519_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5551_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5551_, 0, v___y_5547_);
                leanh::lean_ctor_set(v___x_5551_, 1, v___y_5548_);
                leanh::lean_ctor_set(v___x_5551_, 2, v___y_5549_);
                leanh::lean_ctor_set(v___x_5551_, 3, v_traceTask_5550_);
                v___x_5552_ = lean_array_push(v_snapshotTasks_5545_, v___x_5551_);
                v___x_5553_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5553_, 0, v___y_5542_);
                leanh::lean_ctor_set(v___x_5553_, 1, v___x_5552_);
                v___x_5554_ = lean_io_promise_resolve(v___x_5553_, v___x_5540_);
                leanh::lean_dec(v___x_5540_);
                if leanh::lean_obj_tag(v___y_5543_) == 1 {
                    v_val_5555_ = leanh::lean_ctor_get(v___y_5543_, 0);
                    leanh::lean_inc(v_val_5555_);
                    leanh::lean_dec_ref_known(v___y_5543_, 1);
                    v___x_5556_ = leanh::lean_box(0);
                    v___x_5557_ =
                        l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(
                            v___x_5556_,
                            v_fst_5519_,
                            v___y_5544_,
                            v_val_5555_,
                            v_val_5520_,
                            v___y_5546_,
                            v_a_5521_,
                        );
                    return v___x_5557_;
                } else {
                    leanh::lean_dec_ref(v___y_5546_);
                    leanh::lean_dec_ref(v___y_5544_);
                    leanh::lean_dec(v___y_5543_);
                    leanh::lean_dec_ref(v_fst_5519_);
                    v___x_5558_ = leanh::lean_box(0);
                    return v___x_5558_;
                }
            }
            2 => {
                v_snapshotTasks_5568_ = leanh::lean_ctor_get(v___y_5562_, 10);
                leanh::lean_inc_ref(v_snapshotTasks_5568_);
                v___x_5569_ = lean_mk_empty_array_with_capacity(v___y_5567_);
                leanh::lean_dec(v___y_5567_);
                leanh::lean_inc_ref(v___y_5560_);
                v___x_5570_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5570_, 0, v___y_5560_);
                leanh::lean_ctor_set(v___x_5570_, 1, v___x_5569_);
                v___x_5571_ = lean_task_pure(v___x_5570_);
                v___y_5542_ = v___y_5560_;
                v___y_5543_ = v___y_5561_;
                v___y_5544_ = v___y_5562_;
                v_snapshotTasks_5545_ = v_snapshotTasks_5568_;
                v___y_5546_ = v___y_5563_;
                v___y_5547_ = v___y_5564_;
                v___y_5548_ = v___y_5565_;
                v___y_5549_ = v___y_5566_;
                v_traceTask_5550_ = v___x_5571_;
                state = 1;
                continue;
            }
            3 => {
                v___x_5604_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_5586_);
                v___x_5605_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_5605_, 0, v___y_5598_);
                leanh::lean_ctor_set(v___x_5605_, 1, v___x_5604_);
                leanh::lean_ctor_set(v___x_5605_, 2, v___y_5591_);
                leanh::lean_ctor_set(v___x_5605_, 3, v_traceState_5589_);
                leanh::lean_ctor_set_uint8(
                    v___x_5605_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v_val_5520_,
                );
                v___x_5606_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5606_, 0, v___x_5605_);
                leanh::lean_ctor_set(v___x_5606_, 1, v_reportedCmdState_5603_);
                v___x_5607_ = lean_io_promise_resolve(v___x_5606_, v___x_5538_);
                leanh::lean_dec(v___x_5538_);
                v___x_5608_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_5588_);
                leanh::lean_inc(v___y_5599_);
                v___x_5609_ =
                    l_BaseIO_chainTask___redArg(v___x_5608_, v___y_5593_, v___y_5599_, v___x_5524_);
                v___x_5610_ = l_Lean_inheritedTraceOptions;
                v___x_5611_ = lean_st_ref_get(v___x_5610_);
                v___x_5612_ = l_List_head_x21___redArg(v___x_5526_, v_scopes_5587_);
                leanh::lean_dec(v_scopes_5587_);
                leanh::lean_dec_ref(v___x_5526_);
                v_opts_5613_ = leanh::lean_ctor_get(v___x_5612_, 1);
                leanh::lean_inc_ref(v_opts_5613_);
                leanh::lean_dec(v___x_5612_);
                v_hasTrace_5614_ = leanh::lean_ctor_get_uint8(
                    v_opts_5613_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_5614_ == 0 {
                    leanh::lean_dec_ref(v_opts_5613_);
                    leanh::lean_dec(v___x_5611_);
                    leanh::lean_dec_ref(v___y_5602_);
                    leanh::lean_dec_ref(v___y_5601_);
                    leanh::lean_dec_ref(v___y_5594_);
                    leanh::lean_dec_ref(v_snapshotTasks_5590_);
                    leanh::lean_dec_ref(v_env_5585_);
                    leanh::lean_dec(v___y_5583_);
                    leanh::lean_dec(v___y_5582_);
                    leanh::lean_dec(v___y_5579_);
                    leanh::lean_dec_ref(v___y_5578_);
                    leanh::lean_dec_ref(v___y_5577_);
                    leanh::lean_dec(v___y_5576_);
                    leanh::lean_dec(v___y_5574_);
                    leanh::lean_dec(v___y_5573_);
                    leanh::lean_dec(v_pos_5530_);
                    leanh::lean_dec_ref(v___f_5529_);
                    leanh::lean_dec_ref(v___f_5528_);
                    leanh::lean_dec_ref(v___f_5527_);
                    leanh::lean_dec(v___x_5523_);
                    v___y_5560_ = v___y_5595_;
                    v___y_5561_ = v___y_5581_;
                    v___y_5562_ = v___y_5584_;
                    v___y_5563_ = v___y_5592_;
                    v___y_5564_ = v___y_5596_;
                    v___y_5565_ = v___y_5597_;
                    v___y_5566_ = v___y_5600_;
                    v___y_5567_ = v___y_5599_;
                    state = 2;
                    continue;
                } else {
                    v___x_5615_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
                    v___x_5616_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v___x_5611_,
                        v_opts_5613_,
                        v___x_5615_,
                    );
                    leanh::lean_dec(v___x_5611_);
                    if v___x_5616_ == 0 {
                        leanh::lean_dec_ref(v_opts_5613_);
                        leanh::lean_dec_ref(v___y_5602_);
                        leanh::lean_dec_ref(v___y_5601_);
                        leanh::lean_dec_ref(v___y_5594_);
                        leanh::lean_dec_ref(v_snapshotTasks_5590_);
                        leanh::lean_dec_ref(v_env_5585_);
                        leanh::lean_dec(v___y_5583_);
                        leanh::lean_dec(v___y_5582_);
                        leanh::lean_dec(v___y_5579_);
                        leanh::lean_dec_ref(v___y_5578_);
                        leanh::lean_dec_ref(v___y_5577_);
                        leanh::lean_dec(v___y_5576_);
                        leanh::lean_dec(v___y_5574_);
                        leanh::lean_dec(v___y_5573_);
                        leanh::lean_dec(v_pos_5530_);
                        leanh::lean_dec_ref(v___f_5529_);
                        leanh::lean_dec_ref(v___f_5528_);
                        leanh::lean_dec_ref(v___f_5527_);
                        leanh::lean_dec(v___x_5523_);
                        v___y_5560_ = v___y_5595_;
                        v___y_5561_ = v___y_5581_;
                        v___y_5562_ = v___y_5584_;
                        v___y_5563_ = v___y_5592_;
                        v___y_5564_ = v___y_5596_;
                        v___y_5565_ = v___y_5597_;
                        v___y_5566_ = v___y_5600_;
                        v___y_5567_ = v___y_5599_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc_n(v___y_5599_, 3);
                        v___x_5617_ =
                            lean_task_map(v___f_5527_, v___y_5594_, v___y_5599_, v___x_5524_);
                        leanh::lean_inc_n(v___y_5600_, 3);
                        leanh::lean_inc_n(v___y_5582_, 2);
                        leanh::lean_inc_n(v___y_5583_, 2);
                        v___x_5618_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_5618_, 0, v___y_5583_);
                        leanh::lean_ctor_set(v___x_5618_, 1, v___y_5582_);
                        leanh::lean_ctor_set(v___x_5618_, 2, v___y_5600_);
                        leanh::lean_ctor_set(v___x_5618_, 3, v___x_5617_);
                        v___x_5619_ =
                            lean_task_map(v___f_5528_, v___y_5602_, v___y_5599_, v___x_5524_);
                        v___x_5620_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_5620_, 0, v___y_5583_);
                        leanh::lean_ctor_set(v___x_5620_, 1, v___y_5582_);
                        leanh::lean_ctor_set(v___x_5620_, 2, v___y_5600_);
                        leanh::lean_ctor_set(v___x_5620_, 3, v___x_5619_);
                        v___x_5621_ =
                            lean_task_map(v___f_5529_, v___y_5601_, v___y_5599_, v___x_5524_);
                        v___x_5622_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_5622_, 0, v___y_5583_);
                        leanh::lean_ctor_set(v___x_5622_, 1, v___y_5582_);
                        leanh::lean_ctor_set(v___x_5622_, 2, v___y_5600_);
                        leanh::lean_ctor_set(v___x_5622_, 3, v___x_5621_);
                        v___x_5623_ = leanh::lean_unsigned_to_nat(3);
                        v___x_5624_ = lean_mk_empty_array_with_capacity(v___x_5623_);
                        v___x_5625_ = lean_array_push(v___x_5624_, v___x_5618_);
                        v___x_5626_ = lean_array_push(v___x_5625_, v___x_5620_);
                        v___x_5627_ = lean_array_push(v___x_5626_, v___x_5622_);
                        v___x_5628_ = l_Array_append___redArg(v___x_5627_, v_snapshotTasks_5590_);
                        leanh::lean_inc_ref(v___y_5595_);
                        v___x_5629_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5629_, 0, v___y_5595_);
                        leanh::lean_ctor_set(v___x_5629_, 1, v___x_5628_);
                        leanh::lean_inc_ref(v___x_5629_);
                        v___x_5630_ = l_Lean_Language_SnapshotTree_waitAll(v___x_5629_);
                        v___x_5631_ = leanh::lean_box_usize(v___y_5575_);
                        v___x_5632_ = leanh::lean_box((v___x_5524_) as usize);
                        v___x_5633_ = leanh::lean_box((v_val_5520_) as usize);
                        v___x_5634_ = leanh::lean_box((v___x_5616_) as usize);
                        leanh::lean_inc_ref(v_a_5521_);
                        leanh::lean_inc_ref(v___y_5580_);
                        v___f_5635_ = leanh::lean_alloc_closure(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed as *mut core::ffi::c_void, 20, 18);
                        leanh::lean_closure_set(v___f_5635_, 0, v___x_5523_);
                        leanh::lean_closure_set(v___f_5635_, 1, v___y_5574_);
                        leanh::lean_closure_set(v___f_5635_, 2, v___y_5576_);
                        leanh::lean_closure_set(v___f_5635_, 3, v___x_5631_);
                        leanh::lean_closure_set(v___f_5635_, 4, v___x_5632_);
                        leanh::lean_closure_set(v___f_5635_, 5, v_env_5585_);
                        leanh::lean_closure_set(v___f_5635_, 6, v___y_5580_);
                        leanh::lean_closure_set(v___f_5635_, 7, v___x_5610_);
                        leanh::lean_closure_set(v___f_5635_, 8, v_a_5521_);
                        leanh::lean_closure_set(v___f_5635_, 9, v_opts_5613_);
                        leanh::lean_closure_set(v___f_5635_, 10, v___x_5629_);
                        leanh::lean_closure_set(v___f_5635_, 11, v_pos_5530_);
                        leanh::lean_closure_set(v___f_5635_, 12, v___x_5633_);
                        leanh::lean_closure_set(v___f_5635_, 13, v___y_5577_);
                        leanh::lean_closure_set(v___f_5635_, 14, v___y_5579_);
                        leanh::lean_closure_set(v___f_5635_, 15, v___y_5578_);
                        leanh::lean_closure_set(v___f_5635_, 16, v___y_5573_);
                        leanh::lean_closure_set(v___f_5635_, 17, v___x_5634_);
                        v___x_5636_ =
                            lean_io_bind_task(v___x_5630_, v___f_5635_, v___y_5599_, v_val_5520_);
                        v___y_5542_ = v___y_5595_;
                        v___y_5543_ = v___y_5581_;
                        v___y_5544_ = v___y_5584_;
                        v_snapshotTasks_5545_ = v_snapshotTasks_5590_;
                        v___y_5546_ = v___y_5592_;
                        v___y_5547_ = v___y_5596_;
                        v___y_5548_ = v___y_5597_;
                        v___y_5549_ = v___y_5600_;
                        v_traceTask_5550_ = v___x_5636_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                v_env_5663_ = leanh::lean_ctor_get(v___y_5649_, 0);
                leanh::lean_inc_ref(v_env_5663_);
                v_messages_5664_ = leanh::lean_ctor_get(v___y_5649_, 1);
                leanh::lean_inc_ref(v_messages_5664_);
                v_scopes_5665_ = leanh::lean_ctor_get(v___y_5649_, 2);
                leanh::lean_inc(v_scopes_5665_);
                v_infoState_5666_ = leanh::lean_ctor_get(v___y_5649_, 8);
                leanh::lean_inc_ref(v_infoState_5666_);
                v_traceState_5667_ = leanh::lean_ctor_get(v___y_5649_, 9);
                leanh::lean_inc_ref(v_traceState_5667_);
                v_snapshotTasks_5668_ = leanh::lean_ctor_get(v___y_5649_, 10);
                leanh::lean_inc_ref(v_snapshotTasks_5668_);
                v___y_5573_ = v___y_5639_;
                v___y_5574_ = v___y_5638_;
                v___y_5575_ = v___y_5640_;
                v___y_5576_ = v___y_5641_;
                v___y_5577_ = v___y_5642_;
                v___y_5578_ = v___y_5644_;
                v___y_5579_ = v___y_5643_;
                v___y_5580_ = v___y_5645_;
                v___y_5581_ = v___y_5646_;
                v___y_5582_ = v___y_5647_;
                v___y_5583_ = v___y_5648_;
                v___y_5584_ = v___y_5649_;
                v_env_5585_ = v_env_5663_;
                v_messages_5586_ = v_messages_5664_;
                v_scopes_5587_ = v_scopes_5665_;
                v_infoState_5588_ = v_infoState_5666_;
                v_traceState_5589_ = v_traceState_5667_;
                v_snapshotTasks_5590_ = v_snapshotTasks_5668_;
                v___y_5591_ = v___y_5650_;
                v___y_5592_ = v___y_5651_;
                v___y_5593_ = v___y_5652_;
                v___y_5594_ = v___y_5653_;
                v___y_5595_ = v___y_5654_;
                v___y_5596_ = v___y_5655_;
                v___y_5597_ = v___y_5656_;
                v___y_5598_ = v___y_5657_;
                v___y_5599_ = v___y_5658_;
                v___y_5600_ = v___y_5659_;
                v___y_5601_ = v___y_5660_;
                v___y_5602_ = v___y_5661_;
                v_reportedCmdState_5603_ = v_reportedCmdState_5662_;
                state = 3;
                continue;
            }
            5 => {
                v___x_5697_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5697_, 0, v___y_5696_);
                leanh::lean_ctor_set(v___x_5697_, 1, v___x_5537_);
                leanh::lean_inc_ref(v___y_5684_);
                leanh::lean_inc_n(v_pos_5530_, 2);
                leanh::lean_inc(v_fst_5531_);
                v___x_5698_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(
                    v_fst_5531_,
                    v_cmdState_5532_,
                    v_pos_5530_,
                    v___x_5697_,
                    v___y_5684_,
                    v_a_5521_,
                );
                v___x_5699_ = leanh::lean_box((v_val_5520_) as usize);
                v___x_5700_ = leanh::lean_box((v___x_5524_) as usize);
                leanh::lean_inc_ref(v_a_5521_);
                leanh::lean_inc(v___y_5674_);
                leanh::lean_inc_ref(v___x_5526_);
                leanh::lean_inc_ref(v___x_5698_);
                leanh::lean_inc_ref(v___y_5678_);
                leanh::lean_inc_ref(v___y_5675_);
                v___f_5701_ = leanh::lean_alloc_closure(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed as *mut core::ffi::c_void, 12, 10);
                leanh::lean_closure_set(v___f_5701_, 0, v___y_5675_);
                leanh::lean_closure_set(v___f_5701_, 1, v___y_5678_);
                leanh::lean_closure_set(v___f_5701_, 2, v___x_5699_);
                leanh::lean_closure_set(v___f_5701_, 3, v___x_5539_);
                leanh::lean_closure_set(v___f_5701_, 4, v___x_5698_);
                leanh::lean_closure_set(v___f_5701_, 5, v___x_5526_);
                leanh::lean_closure_set(v___f_5701_, 6, v___y_5674_);
                leanh::lean_closure_set(v___f_5701_, 7, v___x_5700_);
                leanh::lean_closure_set(v___f_5701_, 8, v_a_5521_);
                leanh::lean_closure_set(v___f_5701_, 9, v_pos_5530_);
                v___x_5702_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_5533_, v___x_5669_);
                if v___x_5702_ == 0 {
                    leanh::lean_dec(v___y_5686_);
                    leanh::lean_dec(v_fst_5531_);
                    leanh::lean_inc_ref(v___x_5698_);
                    v___y_5638_ = v___y_5672_;
                    v___y_5639_ = v___y_5671_;
                    v___y_5640_ = v___y_5673_;
                    v___y_5641_ = v___y_5674_;
                    v___y_5642_ = v___y_5675_;
                    v___y_5643_ = v___y_5677_;
                    v___y_5644_ = v___y_5676_;
                    v___y_5645_ = v___y_5678_;
                    v___y_5646_ = v___y_5679_;
                    v___y_5647_ = v___y_5680_;
                    v___y_5648_ = v___y_5681_;
                    v___y_5649_ = v___x_5698_;
                    v___y_5650_ = v___y_5682_;
                    v___y_5651_ = v___y_5684_;
                    v___y_5652_ = v___f_5701_;
                    v___y_5653_ = v___y_5685_;
                    v___y_5654_ = v___y_5687_;
                    v___y_5655_ = v___y_5689_;
                    v___y_5656_ = v___y_5690_;
                    v___y_5657_ = v___y_5692_;
                    v___y_5658_ = v___y_5693_;
                    v___y_5659_ = v___y_5691_;
                    v___y_5660_ = v___y_5695_;
                    v___y_5661_ = v___y_5694_;
                    v_reportedCmdState_5662_ = v___x_5698_;
                    state = 4;
                    continue;
                } else {
                    v___x_5703_ = l_Lean_Parser_isTerminalCommand(v_fst_5531_);
                    if v___x_5703_ == 0 {
                        if v___x_5702_ == 0 {
                            leanh::lean_dec(v___y_5686_);
                            leanh::lean_inc_ref(v___x_5698_);
                            v___y_5638_ = v___y_5672_;
                            v___y_5639_ = v___y_5671_;
                            v___y_5640_ = v___y_5673_;
                            v___y_5641_ = v___y_5674_;
                            v___y_5642_ = v___y_5675_;
                            v___y_5643_ = v___y_5677_;
                            v___y_5644_ = v___y_5676_;
                            v___y_5645_ = v___y_5678_;
                            v___y_5646_ = v___y_5679_;
                            v___y_5647_ = v___y_5680_;
                            v___y_5648_ = v___y_5681_;
                            v___y_5649_ = v___x_5698_;
                            v___y_5650_ = v___y_5682_;
                            v___y_5651_ = v___y_5684_;
                            v___y_5652_ = v___f_5701_;
                            v___y_5653_ = v___y_5685_;
                            v___y_5654_ = v___y_5687_;
                            v___y_5655_ = v___y_5689_;
                            v___y_5656_ = v___y_5690_;
                            v___y_5657_ = v___y_5692_;
                            v___y_5658_ = v___y_5693_;
                            v___y_5659_ = v___y_5691_;
                            v___y_5660_ = v___y_5695_;
                            v___y_5661_ = v___y_5694_;
                            v_reportedCmdState_5662_ = v___x_5698_;
                            state = 4;
                            continue;
                        } else {
                            v_env_5704_ = leanh::lean_ctor_get(v___x_5698_, 0);
                            leanh::lean_inc_ref_n(v_env_5704_, 2);
                            v_messages_5705_ = leanh::lean_ctor_get(v___x_5698_, 1);
                            leanh::lean_inc_ref(v_messages_5705_);
                            v_scopes_5706_ = leanh::lean_ctor_get(v___x_5698_, 2);
                            leanh::lean_inc(v_scopes_5706_);
                            v_infoState_5707_ = leanh::lean_ctor_get(v___x_5698_, 8);
                            leanh::lean_inc_ref(v_infoState_5707_);
                            v_traceState_5708_ = leanh::lean_ctor_get(v___x_5698_, 9);
                            leanh::lean_inc_ref(v_traceState_5708_);
                            v_snapshotTasks_5709_ = leanh::lean_ctor_get(v___x_5698_, 10);
                            leanh::lean_inc_ref(v_snapshotTasks_5709_);
                            v___x_5710_ = lean_mk_empty_array_with_capacity(v___y_5686_);
                            leanh::lean_dec(v___y_5686_);
                            leanh::lean_inc_ref(v___x_5710_);
                            v___x_5711_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5711_, 0, v___x_5710_);
                            leanh::lean_inc_n(v___y_5693_, 3);
                            v___x_5712_ = leanh::lean_alloc_ctor(
                                0,
                                4,
                                (core::mem::size_of::<usize>() * 1) as u32,
                            );
                            leanh::lean_ctor_set(v___x_5712_, 0, v___x_5711_);
                            leanh::lean_ctor_set(v___x_5712_, 1, v___x_5710_);
                            leanh::lean_ctor_set(v___x_5712_, 2, v___y_5693_);
                            leanh::lean_ctor_set(v___x_5712_, 3, v___y_5693_);
                            leanh::lean_ctor_set_usize(v___x_5712_, 4, v___y_5688_);
                            v___x_5713_ = l_Lean_NameSet_empty;
                            leanh::lean_inc_ref_n(v___x_5712_, 2);
                            v___x_5714_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_5714_, 0, v___x_5712_);
                            leanh::lean_ctor_set(v___x_5714_, 1, v___x_5712_);
                            leanh::lean_ctor_set(v___x_5714_, 2, v___x_5713_);
                            v___x_5715_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0;
                            v___x_5716_ = l_Lean_Options_empty;
                            v___x_5717_ = leanh::lean_box(0);
                            v___x_5718_ = lean_mk_empty_array_with_capacity(v___y_5693_);
                            leanh::lean_inc_ref_n(v___x_5718_, 2);
                            leanh::lean_inc_n(v___x_5523_, 2);
                            v___x_5719_ = leanh::lean_alloc_ctor(0, 10, (3) as u32);
                            leanh::lean_ctor_set(v___x_5719_, 0, v___x_5715_);
                            leanh::lean_ctor_set(v___x_5719_, 1, v___x_5716_);
                            leanh::lean_ctor_set(v___x_5719_, 2, v___x_5523_);
                            leanh::lean_ctor_set(v___x_5719_, 3, v___x_5717_);
                            leanh::lean_ctor_set(v___x_5719_, 4, v___x_5717_);
                            leanh::lean_ctor_set(v___x_5719_, 5, v___x_5718_);
                            leanh::lean_ctor_set(v___x_5719_, 6, v___x_5718_);
                            leanh::lean_ctor_set(v___x_5719_, 7, v___x_5717_);
                            leanh::lean_ctor_set(v___x_5719_, 8, v___x_5717_);
                            leanh::lean_ctor_set(v___x_5719_, 9, v___x_5717_);
                            leanh::lean_ctor_set_uint8(
                                v___x_5719_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                                v_val_5520_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_5719_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 1)
                                    as u32,
                                v_val_5520_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_5719_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 2)
                                    as u32,
                                v_val_5520_,
                            );
                            v___x_5720_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5720_, 0, v___x_5719_);
                            leanh::lean_ctor_set(v___x_5720_, 1, v___x_5717_);
                            v___x_5721_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
                            v___x_5722_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3;
                            v___x_5723_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_5523_);
                            v___x_5724_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
                            v___x_5725_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                            leanh::lean_ctor_set(v___x_5725_, 0, v___x_5724_);
                            leanh::lean_ctor_set(v___x_5725_, 1, v___x_5724_);
                            leanh::lean_ctor_set(v___x_5725_, 2, v___x_5712_);
                            leanh::lean_ctor_set_uint8(
                                v___x_5725_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                                v___x_5524_,
                            );
                            leanh::lean_inc_ref(v___y_5683_);
                            v___x_5726_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                            leanh::lean_ctor_set(v___x_5726_, 0, v_env_5704_);
                            leanh::lean_ctor_set(v___x_5726_, 1, v___x_5714_);
                            leanh::lean_ctor_set(v___x_5726_, 2, v___x_5720_);
                            leanh::lean_ctor_set(v___x_5726_, 3, v___x_5713_);
                            leanh::lean_ctor_set(v___x_5726_, 4, v___x_5721_);
                            leanh::lean_ctor_set(v___x_5726_, 5, v___y_5693_);
                            leanh::lean_ctor_set(v___x_5726_, 6, v___x_5722_);
                            leanh::lean_ctor_set(v___x_5726_, 7, v___x_5723_);
                            leanh::lean_ctor_set(v___x_5726_, 8, v___x_5725_);
                            leanh::lean_ctor_set(v___x_5726_, 9, v___y_5683_);
                            leanh::lean_ctor_set(v___x_5726_, 10, v___x_5718_);
                            v___y_5573_ = v___y_5671_;
                            v___y_5574_ = v___y_5672_;
                            v___y_5575_ = v___y_5673_;
                            v___y_5576_ = v___y_5674_;
                            v___y_5577_ = v___y_5675_;
                            v___y_5578_ = v___y_5676_;
                            v___y_5579_ = v___y_5677_;
                            v___y_5580_ = v___y_5678_;
                            v___y_5581_ = v___y_5679_;
                            v___y_5582_ = v___y_5680_;
                            v___y_5583_ = v___y_5681_;
                            v___y_5584_ = v___x_5698_;
                            v_env_5585_ = v_env_5704_;
                            v_messages_5586_ = v_messages_5705_;
                            v_scopes_5587_ = v_scopes_5706_;
                            v_infoState_5588_ = v_infoState_5707_;
                            v_traceState_5589_ = v_traceState_5708_;
                            v_snapshotTasks_5590_ = v_snapshotTasks_5709_;
                            v___y_5591_ = v___y_5682_;
                            v___y_5592_ = v___y_5684_;
                            v___y_5593_ = v___f_5701_;
                            v___y_5594_ = v___y_5685_;
                            v___y_5595_ = v___y_5687_;
                            v___y_5596_ = v___y_5689_;
                            v___y_5597_ = v___y_5690_;
                            v___y_5598_ = v___y_5692_;
                            v___y_5599_ = v___y_5693_;
                            v___y_5600_ = v___y_5691_;
                            v___y_5601_ = v___y_5695_;
                            v___y_5602_ = v___y_5694_;
                            v_reportedCmdState_5603_ = v___x_5726_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___y_5686_);
                        leanh::lean_inc_ref(v___x_5698_);
                        v___y_5638_ = v___y_5672_;
                        v___y_5639_ = v___y_5671_;
                        v___y_5640_ = v___y_5673_;
                        v___y_5641_ = v___y_5674_;
                        v___y_5642_ = v___y_5675_;
                        v___y_5643_ = v___y_5677_;
                        v___y_5644_ = v___y_5676_;
                        v___y_5645_ = v___y_5678_;
                        v___y_5646_ = v___y_5679_;
                        v___y_5647_ = v___y_5680_;
                        v___y_5648_ = v___y_5681_;
                        v___y_5649_ = v___x_5698_;
                        v___y_5650_ = v___y_5682_;
                        v___y_5651_ = v___y_5684_;
                        v___y_5652_ = v___f_5701_;
                        v___y_5653_ = v___y_5685_;
                        v___y_5654_ = v___y_5687_;
                        v___y_5655_ = v___y_5689_;
                        v___y_5656_ = v___y_5690_;
                        v___y_5657_ = v___y_5692_;
                        v___y_5658_ = v___y_5693_;
                        v___y_5659_ = v___y_5691_;
                        v___y_5660_ = v___y_5695_;
                        v___y_5661_ = v___y_5694_;
                        v_reportedCmdState_5662_ = v___x_5698_;
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5733_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_5522_);
                v___x_5734_ = l_IO_CancelToken_new();
                v___x_5735_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0;
                leanh::lean_inc(v___x_5523_);
                v___x_5736_ = l_Lean_Name_str___override(v___x_5523_, v___x_5735_);
                v___x_5737_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2;
                v___x_5738_ = l_Lean_Name_str___override(v___x_5736_, v___x_5737_);
                v___x_5739_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4;
                v___x_5740_ = l_Lean_Name_str___override(v___x_5738_, v___x_5739_);
                v___x_5741_ = l_Lean_Name_str___override(v___x_5740_, v___x_5737_);
                v___x_5742_ = leanh::lean_unsigned_to_nat(0);
                v___x_5743_ = l_Lean_Name_num___override(v___x_5741_, v___x_5742_);
                v___x_5744_ = l_Lean_Name_str___override(v___x_5743_, v___x_5737_);
                v___x_5745_ = l_Lean_Name_str___override(v___x_5744_, v___x_5739_);
                v___x_5746_ = l_Lean_Name_str___override(v___x_5745_, v___x_5737_);
                v___x_5747_ =
                    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0;
                v___x_5748_ = l_Lean_Name_str___override(v___x_5746_, v___x_5747_);
                v___x_5749_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5;
                v___x_5750_ = l_Lean_Name_str___override(v___x_5748_, v___x_5749_);
                v___x_5751_ = l_Lean_Name_toString(v___x_5750_, v___x_5524_);
                v___x_5752_ = leanh::lean_box(0);
                v___x_5753_ = leanh::lean_unsigned_to_nat(32);
                v___x_5754_ = lean_mk_empty_array_with_capacity(v___x_5753_);
                leanh::lean_dec_ref(v___x_5754_);
                v___x_5755_ = 5usize;
                v___x_5756_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
                leanh::lean_inc_ref_n(v___x_5751_, 2);
                v___x_5757_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_5757_, 0, v___x_5751_);
                leanh::lean_ctor_set(v___x_5757_, 1, v___x_5733_);
                leanh::lean_ctor_set(v___x_5757_, 2, v___x_5752_);
                leanh::lean_ctor_set(v___x_5757_, 3, v___x_5756_);
                leanh::lean_ctor_set_uint8(
                    v___x_5757_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v_val_5520_,
                );
                v___x_5758_ = l_Lean_Language_Snapshot_Diagnostics_empty;
                v___x_5759_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_5759_, 0, v___x_5751_);
                leanh::lean_ctor_set(v___x_5759_, 1, v___x_5758_);
                leanh::lean_ctor_set(v___x_5759_, 2, v___x_5752_);
                leanh::lean_ctor_set(v___x_5759_, 3, v___x_5756_);
                leanh::lean_ctor_set_uint8(
                    v___x_5759_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v_val_5520_,
                );
                leanh::lean_inc(v___y_5729_);
                v___x_5760_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5760_, 0, v___y_5729_);
                v___x_5761_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_5760_);
                leanh::lean_inc_ref(v___x_5734_);
                v___x_5762_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5762_, 0, v___x_5734_);
                v___x_5763_ = l_IO_Promise_result_x21___redArg(v___x_5537_);
                leanh::lean_inc_ref(v___x_5763_);
                leanh::lean_inc(v___x_5761_);
                leanh::lean_inc_ref_n(v___x_5760_, 3);
                v___x_5764_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5764_, 0, v___x_5760_);
                leanh::lean_ctor_set(v___x_5764_, 1, v___x_5761_);
                leanh::lean_ctor_set(v___x_5764_, 2, v___x_5762_);
                leanh::lean_ctor_set(v___x_5764_, 3, v___x_5763_);
                v___x_5765_ = l_IO_Promise_result_x21___redArg(v___x_5538_);
                leanh::lean_inc_ref(v___x_5765_);
                leanh::lean_inc_n(v___y_5731_, 3);
                v___x_5766_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5766_, 0, v___x_5760_);
                leanh::lean_ctor_set(v___x_5766_, 1, v___y_5731_);
                leanh::lean_ctor_set(v___x_5766_, 2, v___x_5752_);
                leanh::lean_ctor_set(v___x_5766_, 3, v___x_5765_);
                v___x_5767_ = l_IO_Promise_result_x21___redArg(v___x_5539_);
                leanh::lean_inc_ref(v___x_5767_);
                v___x_5768_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5768_, 0, v___x_5760_);
                leanh::lean_ctor_set(v___x_5768_, 1, v___y_5731_);
                leanh::lean_ctor_set(v___x_5768_, 2, v___x_5752_);
                leanh::lean_ctor_set(v___x_5768_, 3, v___x_5767_);
                v___x_5769_ = l_IO_Promise_result_x21___redArg(v___x_5540_);
                v___x_5770_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5770_, 0, v___x_5752_);
                leanh::lean_ctor_set(v___x_5770_, 1, v___y_5731_);
                leanh::lean_ctor_set(v___x_5770_, 2, v___x_5752_);
                leanh::lean_ctor_set(v___x_5770_, 3, v___x_5769_);
                leanh::lean_inc_ref(v___x_5759_);
                v___x_5771_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5771_, 0, v___x_5759_);
                leanh::lean_ctor_set(v___x_5771_, 1, v___x_5764_);
                leanh::lean_ctor_set(v___x_5771_, 2, v___x_5766_);
                leanh::lean_ctor_set(v___x_5771_, 3, v___x_5768_);
                leanh::lean_ctor_set(v___x_5771_, 4, v___x_5770_);
                v___x_5772_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5772_, 0, v___x_5757_);
                leanh::lean_ctor_set(v___x_5772_, 1, v___y_5729_);
                leanh::lean_ctor_set(v___x_5772_, 2, v___y_5730_);
                leanh::lean_ctor_set(v___x_5772_, 3, v___x_5771_);
                leanh::lean_ctor_set(v___x_5772_, 4, v___y_5732_);
                v___x_5773_ = lean_io_promise_resolve(v___x_5772_, v_prom_5525_);
                if leanh::lean_obj_tag(v_old_x3f_5534_) == 0 {
                    leanh::lean_inc_ref(v___x_5759_);
                    leanh::lean_inc_ref(v___x_5751_);
                    v___y_5671_ = v___x_5752_;
                    v___y_5672_ = v___x_5753_;
                    v___y_5673_ = v___x_5755_;
                    v___y_5674_ = v___x_5742_;
                    v___y_5675_ = v___x_5751_;
                    v___y_5676_ = v___x_5759_;
                    v___y_5677_ = v___x_5752_;
                    v___y_5678_ = v___x_5756_;
                    v___y_5679_ = v___y_5728_;
                    v___y_5680_ = v___x_5761_;
                    v___y_5681_ = v___x_5760_;
                    v___y_5682_ = v___x_5752_;
                    v___y_5683_ = v___x_5756_;
                    v___y_5684_ = v___x_5734_;
                    v___y_5685_ = v___x_5763_;
                    v___y_5686_ = v___x_5753_;
                    v___y_5687_ = v___x_5759_;
                    v___y_5688_ = v___x_5755_;
                    v___y_5689_ = v___x_5752_;
                    v___y_5690_ = v___y_5731_;
                    v___y_5691_ = v___x_5752_;
                    v___y_5692_ = v___x_5751_;
                    v___y_5693_ = v___x_5742_;
                    v___y_5694_ = v___x_5765_;
                    v___y_5695_ = v___x_5767_;
                    v___y_5696_ = v___x_5752_;
                    state = 5;
                    continue;
                } else {
                    v_val_5774_ = leanh::lean_ctor_get(v_old_x3f_5534_, 0);
                    v_isSharedCheck_5785_ =
                        (!leanh::lean_is_exclusive(v_old_x3f_5534_)) as u8;
                    if v_isSharedCheck_5785_ == 0 {
                        v___x_5776_ = v_old_x3f_5534_;
                        v_isShared_5777_ = v_isSharedCheck_5785_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5774_);
                        leanh::lean_dec(v_old_x3f_5534_);
                        v___x_5776_ = leanh::lean_box(0);
                        v_isShared_5777_ = v_isSharedCheck_5785_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v_elabSnap_5778_ = leanh::lean_ctor_get(v_val_5774_, 3);
                leanh::lean_inc_ref(v_elabSnap_5778_);
                v_stx_5779_ = leanh::lean_ctor_get(v_val_5774_, 1);
                leanh::lean_inc(v_stx_5779_);
                leanh::lean_dec(v_val_5774_);
                v_elabSnap_5780_ = leanh::lean_ctor_get(v_elabSnap_5778_, 1);
                leanh::lean_inc_ref(v_elabSnap_5780_);
                leanh::lean_dec_ref(v_elabSnap_5778_);
                v___x_5781_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5781_, 0, v_stx_5779_);
                leanh::lean_ctor_set(v___x_5781_, 1, v_elabSnap_5780_);
                if v_isShared_5777_ == 0 {
                    leanh::lean_ctor_set(v___x_5776_, 0, v___x_5781_);
                    v___x_5783_ = v___x_5776_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5784_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5784_, 0, v___x_5781_);
                    v___x_5783_ = v_reuseFailAlloc_5784_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                leanh::lean_inc_ref(v___x_5759_);
                leanh::lean_inc_ref(v___x_5751_);
                v___y_5671_ = v___x_5752_;
                v___y_5672_ = v___x_5753_;
                v___y_5673_ = v___x_5755_;
                v___y_5674_ = v___x_5742_;
                v___y_5675_ = v___x_5751_;
                v___y_5676_ = v___x_5759_;
                v___y_5677_ = v___x_5752_;
                v___y_5678_ = v___x_5756_;
                v___y_5679_ = v___y_5728_;
                v___y_5680_ = v___x_5761_;
                v___y_5681_ = v___x_5760_;
                v___y_5682_ = v___x_5752_;
                v___y_5683_ = v___x_5756_;
                v___y_5684_ = v___x_5734_;
                v___y_5685_ = v___x_5763_;
                v___y_5686_ = v___x_5753_;
                v___y_5687_ = v___x_5759_;
                v___y_5688_ = v___x_5755_;
                v___y_5689_ = v___x_5752_;
                v___y_5690_ = v___y_5731_;
                v___y_5691_ = v___x_5752_;
                v___y_5692_ = v___x_5751_;
                v___y_5693_ = v___x_5742_;
                v___y_5694_ = v___x_5765_;
                v___y_5695_ = v___x_5767_;
                v___y_5696_ = v___x_5783_;
                state = 5;
                continue;
            }
            9 => {
                v___x_5790_ =
                    l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_5789_);
                leanh::lean_inc(v_fst_5531_);
                v___x_5791_ = l_Lean_Parser_isTerminalCommand(v_fst_5531_);
                if v___x_5791_ == 0 {
                    v___x_5792_ = lean_io_promise_new();
                    v_toProcessingContext_5793_ = leanh::lean_ctor_get(v_a_5521_, 0);
                    v_pos_5794_ = leanh::lean_ctor_get(v_fst_5519_, 0);
                    v_endPos_5795_ = leanh::lean_ctor_get(v_toProcessingContext_5793_, 3);
                    leanh::lean_inc(v___x_5792_);
                    v___x_5796_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5796_, 0, v___x_5792_);
                    v___x_5797_ = leanh::lean_box(0);
                    leanh::lean_inc(v_endPos_5795_);
                    leanh::lean_inc(v_pos_5794_);
                    v___x_5798_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5798_, 0, v_pos_5794_);
                    leanh::lean_ctor_set(v___x_5798_, 1, v_endPos_5795_);
                    v___x_5799_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5799_, 0, v___x_5798_);
                    v___x_5800_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5800_, 0, v_parseCancelTk_5535_);
                    v___x_5801_ = l_IO_Promise_result_x21___redArg(v___x_5792_);
                    leanh::lean_dec(v___x_5792_);
                    v___x_5802_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_5802_, 0, v___x_5797_);
                    leanh::lean_ctor_set(v___x_5802_, 1, v___x_5799_);
                    leanh::lean_ctor_set(v___x_5802_, 2, v___x_5800_);
                    leanh::lean_ctor_set(v___x_5802_, 3, v___x_5801_);
                    v___x_5803_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5803_, 0, v___x_5802_);
                    v___y_5728_ = v___x_5796_;
                    v___y_5729_ = v___y_5787_;
                    v___y_5730_ = v___y_5788_;
                    v___y_5731_ = v___x_5790_;
                    v___y_5732_ = v___x_5803_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_parseCancelTk_5535_);
                    v___x_5804_ = leanh::lean_box(0);
                    v___y_5728_ = v___x_5804_;
                    v___y_5729_ = v___y_5787_;
                    v___y_5730_ = v___y_5788_;
                    v___y_5731_ = v___x_5790_;
                    v___y_5732_ = v___x_5804_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                leanh::lean_inc(v_fst_5531_);
                v___x_5808_ =
                    l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(
                        v_fst_5531_,
                    );
                if leanh::lean_obj_tag(v___x_5808_) == 0 {
                    v___x_5809_ = leanh::lean_box(0);
                    v___y_5787_ = v_fst_5806_;
                    v___y_5788_ = v_snd_5807_;
                    v___y_5789_ = v___x_5809_;
                    state = 9;
                    continue;
                } else {
                    v_val_5810_ = leanh::lean_ctor_get(v___x_5808_, 0);
                    v_isSharedCheck_5818_ = (!leanh::lean_is_exclusive(v___x_5808_)) as u8;
                    if v_isSharedCheck_5818_ == 0 {
                        v___x_5812_ = v___x_5808_;
                        v_isShared_5813_ = v_isSharedCheck_5818_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5810_);
                        leanh::lean_dec(v___x_5808_);
                        v___x_5812_ = leanh::lean_box(0);
                        v_isShared_5813_ = v_isSharedCheck_5818_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                leanh::lean_inc(v_val_5810_);
                v___x_5814_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5814_, 0, v_val_5810_);
                leanh::lean_ctor_set(v___x_5814_, 1, v_val_5810_);
                if v_isShared_5813_ == 0 {
                    leanh::lean_ctor_set(v___x_5812_, 0, v___x_5814_);
                    v___x_5816_ = v___x_5812_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5817_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5817_, 0, v___x_5814_);
                    v___x_5816_ = v_reuseFailAlloc_5817_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___y_5787_ = v_fst_5806_;
                v___y_5788_ = v_snd_5807_;
                v___y_5789_ = v___x_5816_;
                state = 9;
                continue;
            }
            13 => {
                if v___y_5820_ == 0 {
                    leanh::lean_inc_ref(v_fst_5519_);
                    leanh::lean_inc(v_fst_5531_);
                    v_fst_5806_ = v_fst_5531_;
                    v_snd_5807_ = v_fst_5519_;
                    state = 10;
                    continue;
                } else {
                    v___x_5821_ = leanh::lean_box(0);
                    v___x_5822_ = l_Lean_Parser_instInhabitedModuleParserState_default;
                    v_fst_5806_ = v___x_5821_;
                    v_snd_5807_ = v___x_5822_;
                    state = 10;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_5825_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_val_5826_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_a_5827_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_snd_5828_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_5829_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_5830_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_prom_5831_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_5832_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___f_5833_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___f_5834_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___f_5835_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_pos_5836_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_fst_5837_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_cmdState_5838_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_opts_5839_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_old_x3f_5840_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_parseCancelTk_5841_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_5842_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_val_45703__boxed_5843_: u8 = 0;
    let mut v___x_45706__boxed_5844_: u8 = 0;
    let mut v_res_5845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_45703__boxed_5843_ = (leanh::lean_unbox(v_val_5826_) as u8);
    v___x_45706__boxed_5844_ = (leanh::lean_unbox(v___x_5830_) as u8);
    v_res_5845_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(
        v_fst_5825_,
        v_val_45703__boxed_5843_,
        v_a_5827_,
        v_snd_5828_,
        v___x_5829_,
        v___x_45706__boxed_5844_,
        v_prom_5831_,
        v___x_5832_,
        v___f_5833_,
        v___f_5834_,
        v___f_5835_,
        v_pos_5836_,
        v_fst_5837_,
        v_cmdState_5838_,
        v_opts_5839_,
        v_old_x3f_5840_,
        v_parseCancelTk_5841_,
    );
    leanh::lean_dec_ref(v_opts_5839_);
    leanh::lean_dec(v_prom_5831_);
    leanh::lean_dec_ref(v_a_5827_);
    return v_res_5845_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(
    mut v_old_x3f_5848_: *mut leanh::LeanObject,
    mut v_parserState_5849_: *mut leanh::LeanObject,
    mut v_cmdState_5850_: *mut leanh::LeanObject,
    mut v_prom_5851_: *mut leanh::LeanObject,
    mut v_sync_5852_: u8,
    mut v_parseCancelTk_5853_: *mut leanh::LeanObject,
    mut v_a_5854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSnapshot_5857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserState_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elabSnap_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newParserState_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultSnap_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5869_: u8 = 0;
    let mut v___x_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: u8 = 0;
    let mut v___x_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toProcessingContext_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5889_: u8 = 0;
    let mut v_unused_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5898_: u8 = 0;
    let mut v___y_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: u8 = 0;
    let mut v___x_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5935_: u8 = 0;
    let mut v___y_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5951_: u8 = 0;
    let mut v___y_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5954_: u8 = 0;
    let mut v___y_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: u8 = 0;
    let mut v___x_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5974_: u8 = 0;
    let mut v___y_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5977_: u8 = 0;
    let mut v___y_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5989_: u8 = 0;
    let mut v___x_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5994_: u8 = 0;
    let mut v___y_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6002_: u8 = 0;
    let mut v___y_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6005_: u8 = 0;
    let mut v___y_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6011_: u8 = 0;
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: u8 = 0;
    let mut v___x_6026_: u8 = 0;
    let mut v___x_6027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: u8 = 0;
    let mut v___x_6033_: u8 = 0;
    let mut v___x_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_6041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: u8 = 0;
    let mut v___x_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: u8 = 0;
    let mut v___x_6047_: usize = 0;
    let mut v___x_6048_: usize = 0;
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: usize = 0;
    let mut v___x_6051_: usize = 0;
    let mut v___x_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSnapshot_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserState_6073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elabSnap_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCmdSnap_x3f_6075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: u8 = 0;
    let mut v_val_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCmdSnap_x3f_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSnapshot_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserState_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elabSnap_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCmdSnap_x3f_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserState_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5938_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2;
                v___f_5939_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3;
                v___f_5940_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4;
                v___x_5941_ = l_Lean_Elab_Command_instInhabitedScope_default;
                if leanh::lean_obj_tag(v_old_x3f_5848_) == 1 {
                    v_val_6086_ = leanh::lean_ctor_get(v_old_x3f_5848_, 0);
                    v_nextCmdSnap_x3f_6087_ = leanh::lean_ctor_get(v_val_6086_, 4);
                    if leanh::lean_obj_tag(v_nextCmdSnap_x3f_6087_) == 0 {
                        state = 14;
                        continue;
                    } else {
                        v_toSnapshot_6088_ = leanh::lean_ctor_get(v_val_6086_, 0);
                        v_stx_6089_ = leanh::lean_ctor_get(v_val_6086_, 1);
                        v_parserState_6090_ = leanh::lean_ctor_get(v_val_6086_, 2);
                        v_elabSnap_6091_ = leanh::lean_ctor_get(v_val_6086_, 3);
                        v_val_6092_ = leanh::lean_ctor_get(v_nextCmdSnap_x3f_6087_, 0);
                        leanh::lean_inc(v_val_6092_);
                        v___x_6093_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_6092_);
                        if leanh::lean_obj_tag(v___x_6093_) == 1 {
                            v_val_6094_ = leanh::lean_ctor_get(v___x_6093_, 0);
                            leanh::lean_inc(v_val_6094_);
                            leanh::lean_dec_ref_known(v___x_6093_, 1);
                            v_nextCmdSnap_x3f_6095_ = leanh::lean_ctor_get(v_val_6094_, 4);
                            leanh::lean_inc(v_nextCmdSnap_x3f_6095_);
                            leanh::lean_dec(v_val_6094_);
                            if leanh::lean_obj_tag(v_nextCmdSnap_x3f_6095_) == 0 {
                                state = 14;
                                continue;
                            } else {
                                v_val_6096_ =
                                    leanh::lean_ctor_get(v_nextCmdSnap_x3f_6095_, 0);
                                leanh::lean_inc(v_val_6096_);
                                leanh::lean_dec_ref_known(v_nextCmdSnap_x3f_6095_, 1);
                                v___x_6097_ =
                                    l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_6096_);
                                if leanh::lean_obj_tag(v___x_6097_) == 1 {
                                    v_val_6098_ = leanh::lean_ctor_get(v___x_6097_, 0);
                                    leanh::lean_inc(v_val_6098_);
                                    leanh::lean_dec_ref_known(v___x_6097_, 1);
                                    v_parserState_6099_ =
                                        leanh::lean_ctor_get(v_val_6098_, 2);
                                    leanh::lean_inc_ref(v_parserState_6099_);
                                    leanh::lean_dec(v_val_6098_);
                                    v_pos_6100_ =
                                        leanh::lean_ctor_get(v_parserState_6099_, 0);
                                    leanh::lean_inc(v_pos_6100_);
                                    leanh::lean_dec_ref(v_parserState_6099_);
                                    v___x_6101_ = l_Lean_Language_Lean_isBeforeEditPos(
                                        v_pos_6100_,
                                        v_a_5854_,
                                    );
                                    leanh::lean_dec(v_pos_6100_);
                                    if v___x_6101_ == 0 {
                                        state = 14;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_val_6092_);
                                        leanh::lean_inc_ref(v_elabSnap_6091_);
                                        leanh::lean_inc_ref_n(v_parserState_6090_, 2);
                                        leanh::lean_inc(v_stx_6089_);
                                        leanh::lean_inc_ref(v_toSnapshot_6088_);
                                        leanh::lean_dec_ref_known(v_old_x3f_5848_, 1);
                                        leanh::lean_dec_ref(v_parseCancelTk_5853_);
                                        leanh::lean_dec_ref(v_cmdState_5850_);
                                        leanh::lean_dec_ref(v_parserState_5849_);
                                        v_toSnapshot_5857_ = v_toSnapshot_6088_;
                                        v_stx_5858_ = v_stx_6089_;
                                        v_parserState_5859_ = v_parserState_6090_;
                                        v_elabSnap_5860_ = v_elabSnap_6091_;
                                        v_val_5861_ = v_val_6092_;
                                        v_newParserState_5862_ = v_parserState_6090_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_6097_);
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_6093_);
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    state = 14;
                    continue;
                }
            }
            1 => {
                v___x_5863_ = lean_io_promise_new();
                v___x_5864_ = l_IO_CancelToken_new();
                v_resultSnap_5865_ = leanh::lean_ctor_get(v_elabSnap_5860_, 2);
                leanh::lean_inc_ref(v_resultSnap_5865_);
                v_task_5866_ = leanh::lean_ctor_get(v_resultSnap_5865_, 3);
                v_isSharedCheck_5889_ =
                    (!leanh::lean_is_exclusive(v_resultSnap_5865_)) as u8;
                if v_isSharedCheck_5889_ == 0 {
                    v_unused_5890_ = leanh::lean_ctor_get(v_resultSnap_5865_, 2);
                    leanh::lean_dec(v_unused_5890_);
                    v_unused_5891_ = leanh::lean_ctor_get(v_resultSnap_5865_, 1);
                    leanh::lean_dec(v_unused_5891_);
                    v_unused_5892_ = leanh::lean_ctor_get(v_resultSnap_5865_, 0);
                    leanh::lean_dec(v_unused_5892_);
                    v___x_5868_ = v_resultSnap_5865_;
                    v_isShared_5869_ = v_isSharedCheck_5889_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_task_5866_);
                    leanh::lean_dec(v_resultSnap_5865_);
                    v___x_5868_ = leanh::lean_box(0);
                    v_isShared_5869_ = v_isSharedCheck_5889_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5870_ = leanh::lean_box((v_sync_5852_) as usize);
                leanh::lean_inc_ref(v_a_5854_);
                leanh::lean_inc_ref(v___x_5864_);
                leanh::lean_inc(v___x_5863_);
                leanh::lean_inc_ref(v_newParserState_5862_);
                v___f_5871_ = leanh::lean_alloc_closure(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed as *mut core::ffi::c_void, 8, 6);
                leanh::lean_closure_set(v___f_5871_, 0, v_val_5861_);
                leanh::lean_closure_set(v___f_5871_, 1, v_newParserState_5862_);
                leanh::lean_closure_set(v___f_5871_, 2, v___x_5863_);
                leanh::lean_closure_set(v___f_5871_, 3, v___x_5870_);
                leanh::lean_closure_set(v___f_5871_, 4, v___x_5864_);
                leanh::lean_closure_set(v___f_5871_, 5, v_a_5854_);
                v___x_5872_ = leanh::lean_unsigned_to_nat(0);
                v___x_5873_ = 1;
                v___x_5874_ = l_BaseIO_chainTask___redArg(
                    v_task_5866_,
                    v___f_5871_,
                    v___x_5872_,
                    v___x_5873_,
                );
                v_toProcessingContext_5875_ = leanh::lean_ctor_get(v_a_5854_, 0);
                v_pos_5876_ = leanh::lean_ctor_get(v_newParserState_5862_, 0);
                leanh::lean_inc(v_pos_5876_);
                leanh::lean_dec_ref(v_newParserState_5862_);
                v_endPos_5877_ = leanh::lean_ctor_get(v_toProcessingContext_5875_, 3);
                v___x_5878_ = leanh::lean_box(0);
                leanh::lean_inc(v_endPos_5877_);
                v___x_5879_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5879_, 0, v_pos_5876_);
                leanh::lean_ctor_set(v___x_5879_, 1, v_endPos_5877_);
                v___x_5880_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5880_, 0, v___x_5879_);
                v___x_5881_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5881_, 0, v___x_5864_);
                v___x_5882_ = l_IO_Promise_result_x21___redArg(v___x_5863_);
                leanh::lean_dec(v___x_5863_);
                if v_isShared_5869_ == 0 {
                    leanh::lean_ctor_set(v___x_5868_, 3, v___x_5882_);
                    leanh::lean_ctor_set(v___x_5868_, 2, v___x_5881_);
                    leanh::lean_ctor_set(v___x_5868_, 1, v___x_5880_);
                    leanh::lean_ctor_set(v___x_5868_, 0, v___x_5878_);
                    v___x_5884_ = v___x_5868_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5888_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5888_, 0, v___x_5878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5888_, 1, v___x_5880_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5888_, 2, v___x_5881_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5888_, 3, v___x_5882_);
                    v___x_5884_ = v_reuseFailAlloc_5888_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5885_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5885_, 0, v___x_5884_);
                v___x_5886_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5886_, 0, v_toSnapshot_5857_);
                leanh::lean_ctor_set(v___x_5886_, 1, v_stx_5858_);
                leanh::lean_ctor_set(v___x_5886_, 2, v_parserState_5859_);
                leanh::lean_ctor_set(v___x_5886_, 3, v_elabSnap_5860_);
                leanh::lean_ctor_set(v___x_5886_, 4, v___x_5885_);
                v___x_5887_ = lean_io_promise_resolve(v___x_5886_, v_prom_5851_);
                leanh::lean_dec(v_prom_5851_);
                return v___x_5887_;
            }
            4 => {
                v___x_5894_ = leanh::lean_box(0);
                return v___x_5894_;
            }
            5 => {
                state = 4;
                continue;
            }
            6 => {
                v___x_5901_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0;
                v___x_5902_ = l_Lean_Name_str___override(v___y_5899_, v___x_5901_);
                v___x_5903_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2;
                v___x_5904_ = l_Lean_Name_str___override(v___x_5902_, v___x_5903_);
                v___x_5905_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4;
                v___x_5906_ = l_Lean_Name_str___override(v___x_5904_, v___x_5905_);
                v___x_5907_ = l_Lean_Name_str___override(v___x_5906_, v___x_5903_);
                v___x_5908_ = leanh::lean_unsigned_to_nat(0);
                v___x_5909_ = l_Lean_Name_num___override(v___x_5907_, v___x_5908_);
                v___x_5910_ = l_Lean_Name_str___override(v___x_5909_, v___x_5903_);
                v___x_5911_ = l_Lean_Name_str___override(v___x_5910_, v___x_5905_);
                v___x_5912_ = l_Lean_Name_str___override(v___x_5911_, v___x_5903_);
                v___x_5913_ =
                    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0;
                v___x_5914_ = l_Lean_Name_str___override(v___x_5912_, v___x_5913_);
                v___x_5915_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5;
                v___x_5916_ = l_Lean_Name_str___override(v___x_5914_, v___x_5915_);
                v___x_5917_ = l_Lean_Name_toString(v___x_5916_, v___y_5898_);
                v___x_5918_ = l_Lean_Language_Snapshot_Diagnostics_empty;
                v___x_5919_ = leanh::lean_box(0);
                v___x_5920_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
                v___x_5921_ = 0;
                v___x_5922_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_5922_, 0, v___x_5917_);
                leanh::lean_ctor_set(v___x_5922_, 1, v___x_5918_);
                leanh::lean_ctor_set(v___x_5922_, 2, v___x_5919_);
                leanh::lean_ctor_set(v___x_5922_, 3, v___x_5920_);
                leanh::lean_ctor_set_uint8(
                    v___x_5922_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_5921_,
                );
                v___x_5923_ = leanh::lean_box(0);
                v___x_5924_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
                leanh::lean_inc_ref_n(v___x_5922_, 3);
                v___x_5925_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5925_, 0, v___x_5922_);
                leanh::lean_ctor_set(v___x_5925_, 1, v_cmdState_5850_);
                v___x_5926_ =
                    l_Lean_Language_SnapshotTask_finished___redArg(v___x_5919_, v___x_5925_);
                v___x_5927_ =
                    l_Lean_Language_SnapshotTask_finished___redArg(v___x_5919_, v___x_5922_);
                v___x_5928_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
                v___x_5929_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5929_, 0, v___x_5922_);
                leanh::lean_ctor_set(v___x_5929_, 1, v___x_5924_);
                leanh::lean_ctor_set(v___x_5929_, 2, v___x_5926_);
                leanh::lean_ctor_set(v___x_5929_, 3, v___x_5927_);
                leanh::lean_ctor_set(v___x_5929_, 4, v___x_5928_);
                v___x_5930_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5930_, 0, v___x_5922_);
                leanh::lean_ctor_set(v___x_5930_, 1, v___x_5923_);
                leanh::lean_ctor_set(v___x_5930_, 2, v___y_5900_);
                leanh::lean_ctor_set(v___x_5930_, 3, v___x_5929_);
                leanh::lean_ctor_set(v___x_5930_, 4, v___x_5919_);
                v___x_5931_ = lean_io_promise_resolve(v___x_5930_, v_prom_5851_);
                leanh::lean_dec(v_prom_5851_);
                v___x_5932_ = leanh::lean_box(0);
                return v___x_5932_;
            }
            7 => {
                v___y_5898_ = v___y_5935_;
                v___y_5899_ = v___y_5934_;
                v___y_5900_ = v___y_5936_;
                state = 6;
                continue;
            }
            8 => {
                v___x_5960_ =
                    l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_5959_);
                v___x_5961_ = l_Lean_Parser_isTerminalCommand(v___y_5950_);
                if v___x_5961_ == 0 {
                    v___x_5962_ = lean_io_promise_new();
                    v___x_5963_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5963_, 0, v___x_5962_);
                    v___x_5964_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_5960_, v___y_5945_, v___y_5948_, v___y_5951_, v_a_5854_, v___y_5949_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5952_, v___y_5946_, v___y_5957_, v___y_5943_, v_prom_5851_, v___x_5941_, v___f_5940_, v___f_5939_, v___f_5938_, v___y_5956_, v___y_5958_, v_cmdState_5850_, v___y_5947_, v___y_5944_, v_old_x3f_5848_, v_parseCancelTk_5853_, v___x_5963_);
                    leanh::lean_dec_ref(v___y_5947_);
                    leanh::lean_dec(v_prom_5851_);
                    leanh::lean_dec(v___y_5946_);
                    leanh::lean_dec(v___y_5945_);
                    v___y_5896_ = v___x_5964_;
                    state = 5;
                    continue;
                } else {
                    v___x_5965_ = leanh::lean_box(0);
                    v___x_5966_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_5960_, v___y_5945_, v___y_5948_, v___y_5951_, v_a_5854_, v___y_5949_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5952_, v___y_5946_, v___y_5957_, v___y_5943_, v_prom_5851_, v___x_5941_, v___f_5940_, v___f_5939_, v___f_5938_, v___y_5956_, v___y_5958_, v_cmdState_5850_, v___y_5947_, v___y_5944_, v_old_x3f_5848_, v_parseCancelTk_5853_, v___x_5965_);
                    leanh::lean_dec_ref(v___y_5947_);
                    leanh::lean_dec(v_prom_5851_);
                    leanh::lean_dec(v___y_5946_);
                    leanh::lean_dec(v___y_5945_);
                    v___y_5896_ = v___x_5966_;
                    state = 5;
                    continue;
                }
            }
            9 => {
                leanh::lean_inc(v___y_5981_);
                v___x_5984_ =
                    l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(
                        v___y_5981_,
                    );
                if leanh::lean_obj_tag(v___x_5984_) == 0 {
                    v___x_5985_ = leanh::lean_box(0);
                    v___y_5943_ = v_snd_5983_;
                    v___y_5944_ = v___y_5968_;
                    v___y_5945_ = v___y_5969_;
                    v___y_5946_ = v___y_5970_;
                    v___y_5947_ = v___y_5971_;
                    v___y_5948_ = v___y_5972_;
                    v___y_5949_ = v___y_5973_;
                    v___y_5950_ = v___y_5981_;
                    v___y_5951_ = v___y_5974_;
                    v___y_5952_ = v___y_5975_;
                    v___y_5953_ = v___y_5976_;
                    v___y_5954_ = v___y_5977_;
                    v___y_5955_ = v_fst_5982_;
                    v___y_5956_ = v___y_5978_;
                    v___y_5957_ = v___y_5979_;
                    v___y_5958_ = v___y_5980_;
                    v___y_5959_ = v___x_5985_;
                    state = 8;
                    continue;
                } else {
                    v_val_5986_ = leanh::lean_ctor_get(v___x_5984_, 0);
                    v_isSharedCheck_5994_ = (!leanh::lean_is_exclusive(v___x_5984_)) as u8;
                    if v_isSharedCheck_5994_ == 0 {
                        v___x_5988_ = v___x_5984_;
                        v_isShared_5989_ = v_isSharedCheck_5994_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5986_);
                        leanh::lean_dec(v___x_5984_);
                        v___x_5988_ = leanh::lean_box(0);
                        v_isShared_5989_ = v_isSharedCheck_5994_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                leanh::lean_inc(v_val_5986_);
                v___x_5990_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5990_, 0, v_val_5986_);
                leanh::lean_ctor_set(v___x_5990_, 1, v_val_5986_);
                if v_isShared_5989_ == 0 {
                    leanh::lean_ctor_set(v___x_5988_, 0, v___x_5990_);
                    v___x_5992_ = v___x_5988_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5993_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5993_, 0, v___x_5990_);
                    v___x_5992_ = v_reuseFailAlloc_5993_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_5943_ = v_snd_5983_;
                v___y_5944_ = v___y_5968_;
                v___y_5945_ = v___y_5969_;
                v___y_5946_ = v___y_5970_;
                v___y_5947_ = v___y_5971_;
                v___y_5948_ = v___y_5972_;
                v___y_5949_ = v___y_5973_;
                v___y_5950_ = v___y_5981_;
                v___y_5951_ = v___y_5974_;
                v___y_5952_ = v___y_5975_;
                v___y_5953_ = v___y_5976_;
                v___y_5954_ = v___y_5977_;
                v___y_5955_ = v_fst_5982_;
                v___y_5956_ = v___y_5978_;
                v___y_5957_ = v___y_5979_;
                v___y_5958_ = v___y_5980_;
                v___y_5959_ = v___x_5992_;
                state = 8;
                continue;
            }
            12 => {
                if v___y_6011_ == 0 {
                    leanh::lean_inc(v___y_6010_);
                    v___y_5968_ = v___y_5996_;
                    v___y_5969_ = v___y_5997_;
                    v___y_5970_ = v___y_5998_;
                    v___y_5971_ = v___y_5999_;
                    v___y_5972_ = v___y_6000_;
                    v___y_5973_ = v___y_6001_;
                    v___y_5974_ = v___y_6002_;
                    v___y_5975_ = v___y_6003_;
                    v___y_5976_ = v___y_6004_;
                    v___y_5977_ = v___y_6005_;
                    v___y_5978_ = v___y_6006_;
                    v___y_5979_ = v___y_6008_;
                    v___y_5980_ = v___y_6007_;
                    v___y_5981_ = v___y_6010_;
                    v_fst_5982_ = v___y_6010_;
                    v_snd_5983_ = v___y_6009_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_6009_);
                    v___x_6012_ = leanh::lean_box(0);
                    v___x_6013_ = l_Lean_Parser_instInhabitedModuleParserState_default;
                    v___y_5968_ = v___y_5996_;
                    v___y_5969_ = v___y_5997_;
                    v___y_5970_ = v___y_5998_;
                    v___y_5971_ = v___y_5999_;
                    v___y_5972_ = v___y_6000_;
                    v___y_5973_ = v___y_6001_;
                    v___y_5974_ = v___y_6002_;
                    v___y_5975_ = v___y_6003_;
                    v___y_5976_ = v___y_6004_;
                    v___y_5977_ = v___y_6005_;
                    v___y_5978_ = v___y_6006_;
                    v___y_5979_ = v___y_6008_;
                    v___y_5980_ = v___y_6007_;
                    v___y_5981_ = v___y_6010_;
                    v_fst_5982_ = v___x_6012_;
                    v_snd_5983_ = v___x_6013_;
                    state = 9;
                    continue;
                }
            }
            13 => {
                v___x_6025_ = l_IO_CancelToken_isSet(v_parseCancelTk_5853_);
                v___x_6026_ = 1;
                if v___x_6025_ == 0 {
                    leanh::lean_dec(v___y_6021_);
                    if v_sync_5852_ == 0 {
                        v___x_6027_ = lean_io_promise_new();
                        v___x_6028_ = lean_io_promise_new();
                        v___x_6029_ = lean_io_promise_new();
                        v___x_6030_ = lean_io_promise_new();
                        v___x_6031_ = l_Lean_internal_cmdlineSnapshots;
                        v___x_6032_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_6022_, v___x_6031_);
                        leanh::lean_dec_ref(v___y_6022_);
                        if v___x_6032_ == 0 {
                            v___y_5996_ = v___x_6031_;
                            v___y_5997_ = v___x_6030_;
                            v___y_5998_ = v___x_6028_;
                            v___y_5999_ = v___y_6018_;
                            v___y_6000_ = v___y_6017_;
                            v___y_6001_ = v___y_6020_;
                            v___y_6002_ = v___x_6025_;
                            v___y_6003_ = v___x_6027_;
                            v___y_6004_ = v___y_6016_;
                            v___y_6005_ = v___x_6026_;
                            v___y_6006_ = v___y_6015_;
                            v___y_6007_ = v___y_6019_;
                            v___y_6008_ = v___x_6029_;
                            v___y_6009_ = v___y_6023_;
                            v___y_6010_ = v___y_6024_;
                            v___y_6011_ = v___x_6032_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v___y_6024_);
                            v___x_6033_ = l_Lean_Parser_isTerminalCommand(v___y_6024_);
                            if v___x_6033_ == 0 {
                                v___y_5996_ = v___x_6031_;
                                v___y_5997_ = v___x_6030_;
                                v___y_5998_ = v___x_6028_;
                                v___y_5999_ = v___y_6018_;
                                v___y_6000_ = v___y_6017_;
                                v___y_6001_ = v___y_6020_;
                                v___y_6002_ = v___x_6025_;
                                v___y_6003_ = v___x_6027_;
                                v___y_6004_ = v___y_6016_;
                                v___y_6005_ = v___x_6026_;
                                v___y_6006_ = v___y_6015_;
                                v___y_6007_ = v___y_6019_;
                                v___y_6008_ = v___x_6029_;
                                v___y_6009_ = v___y_6023_;
                                v___y_6010_ = v___y_6024_;
                                v___y_6011_ = v___x_6032_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v___y_6024_);
                                v___y_5968_ = v___x_6031_;
                                v___y_5969_ = v___x_6030_;
                                v___y_5970_ = v___x_6028_;
                                v___y_5971_ = v___y_6018_;
                                v___y_5972_ = v___y_6017_;
                                v___y_5973_ = v___y_6020_;
                                v___y_5974_ = v___x_6025_;
                                v___y_5975_ = v___x_6027_;
                                v___y_5976_ = v___y_6016_;
                                v___y_5977_ = v___x_6026_;
                                v___y_5978_ = v___y_6015_;
                                v___y_5979_ = v___x_6029_;
                                v___y_5980_ = v___y_6019_;
                                v___y_5981_ = v___y_6024_;
                                v_fst_5982_ = v___y_6024_;
                                v_snd_5983_ = v___y_6023_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___y_6024_);
                        leanh::lean_dec_ref(v___y_6023_);
                        leanh::lean_dec_ref(v___y_6022_);
                        v___x_6034_ = leanh::lean_box((v___x_6025_) as usize);
                        v___x_6035_ = leanh::lean_box((v___x_6026_) as usize);
                        leanh::lean_inc_ref(v_a_5854_);
                        v___f_6036_ = leanh::lean_alloc_closure(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed as *mut core::ffi::c_void, 18, 17);
                        leanh::lean_closure_set(v___f_6036_, 0, v___y_6017_);
                        leanh::lean_closure_set(v___f_6036_, 1, v___x_6034_);
                        leanh::lean_closure_set(v___f_6036_, 2, v_a_5854_);
                        leanh::lean_closure_set(v___f_6036_, 3, v___y_6020_);
                        leanh::lean_closure_set(v___f_6036_, 4, v___y_6016_);
                        leanh::lean_closure_set(v___f_6036_, 5, v___x_6035_);
                        leanh::lean_closure_set(v___f_6036_, 6, v_prom_5851_);
                        leanh::lean_closure_set(v___f_6036_, 7, v___x_5941_);
                        leanh::lean_closure_set(v___f_6036_, 8, v___f_5940_);
                        leanh::lean_closure_set(v___f_6036_, 9, v___f_5939_);
                        leanh::lean_closure_set(v___f_6036_, 10, v___f_5938_);
                        leanh::lean_closure_set(v___f_6036_, 11, v___y_6015_);
                        leanh::lean_closure_set(v___f_6036_, 12, v___y_6019_);
                        leanh::lean_closure_set(v___f_6036_, 13, v_cmdState_5850_);
                        leanh::lean_closure_set(v___f_6036_, 14, v___y_6018_);
                        leanh::lean_closure_set(v___f_6036_, 15, v_old_x3f_5848_);
                        leanh::lean_closure_set(v___f_6036_, 16, v_parseCancelTk_5853_);
                        v___x_6037_ = leanh::lean_unsigned_to_nat(0);
                        v___x_6038_ = lean_io_as_task(v___f_6036_, v___x_6037_);
                        leanh::lean_dec_ref(v___x_6038_);
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_6024_);
                    leanh::lean_dec_ref(v___y_6022_);
                    leanh::lean_dec_ref(v___y_6020_);
                    leanh::lean_dec(v___y_6019_);
                    leanh::lean_dec_ref(v___y_6018_);
                    leanh::lean_dec_ref(v___y_6017_);
                    leanh::lean_dec(v___y_6016_);
                    leanh::lean_dec(v___y_6015_);
                    leanh::lean_dec_ref(v_parseCancelTk_5853_);
                    if leanh::lean_obj_tag(v_old_x3f_5848_) == 1 {
                        v_val_6039_ = leanh::lean_ctor_get(v_old_x3f_5848_, 0);
                        leanh::lean_inc(v_val_6039_);
                        leanh::lean_dec_ref_known(v_old_x3f_5848_, 1);
                        v___x_6040_ =
                            l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(
                                v_val_6039_,
                            );
                        v_children_6041_ = leanh::lean_ctor_get(v___x_6040_, 1);
                        leanh::lean_inc_ref(v_children_6041_);
                        leanh::lean_dec_ref(v___x_6040_);
                        v___x_6042_ = leanh::lean_unsigned_to_nat(0);
                        v___x_6043_ = lean_array_get_size(v_children_6041_);
                        v___x_6044_ = lean_nat_dec_lt(v___x_6042_, v___x_6043_);
                        if v___x_6044_ == 0 {
                            leanh::lean_dec_ref(v_children_6041_);
                            v___y_5898_ = v___x_6026_;
                            v___y_5899_ = v___y_6021_;
                            v___y_5900_ = v___y_6023_;
                            state = 6;
                            continue;
                        } else {
                            v___x_6045_ = leanh::lean_box(0);
                            v___x_6046_ = lean_nat_dec_le(v___x_6043_, v___x_6043_);
                            if v___x_6046_ == 0 {
                                if v___x_6044_ == 0 {
                                    leanh::lean_dec_ref(v_children_6041_);
                                    v___y_5898_ = v___x_6026_;
                                    v___y_5899_ = v___y_6021_;
                                    v___y_5900_ = v___y_6023_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_6047_ = 0usize;
                                    v___x_6048_ = lean_usize_of_nat(v___x_6043_);
                                    v___x_6049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_6041_, v___x_6047_, v___x_6048_, v___x_6045_);
                                    leanh::lean_dec_ref(v_children_6041_);
                                    v___y_5934_ = v___y_6021_;
                                    v___y_5935_ = v___x_6026_;
                                    v___y_5936_ = v___y_6023_;
                                    v___y_5937_ = v___x_6049_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v___x_6050_ = 0usize;
                                v___x_6051_ = lean_usize_of_nat(v___x_6043_);
                                v___x_6052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_6041_, v___x_6050_, v___x_6051_, v___x_6045_);
                                leanh::lean_dec_ref(v_children_6041_);
                                v___y_5934_ = v___y_6021_;
                                v___y_5935_ = v___x_6026_;
                                v___y_5936_ = v___y_6023_;
                                v___y_5937_ = v___x_6052_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_old_x3f_5848_);
                        v___y_5898_ = v___x_6026_;
                        v___y_5899_ = v___y_6021_;
                        v___y_5900_ = v___y_6023_;
                        state = 6;
                        continue;
                    }
                }
            }
            14 => {
                v_env_6054_ = leanh::lean_ctor_get(v_cmdState_5850_, 0);
                v_scopes_6055_ = leanh::lean_ctor_get(v_cmdState_5850_, 2);
                v___x_6056_ = l_List_head_x21___redArg(v___x_5941_, v_scopes_6055_);
                v_opts_6057_ = leanh::lean_ctor_get(v___x_6056_, 1);
                leanh::lean_inc_ref_n(v_opts_6057_, 2);
                v_currNamespace_6058_ = leanh::lean_ctor_get(v___x_6056_, 2);
                leanh::lean_inc(v_currNamespace_6058_);
                v_openDecls_6059_ = leanh::lean_ctor_get(v___x_6056_, 3);
                leanh::lean_inc(v_openDecls_6059_);
                leanh::lean_dec(v___x_6056_);
                leanh::lean_inc_ref(v_env_6054_);
                v___x_6060_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_6060_, 0, v_env_6054_);
                leanh::lean_ctor_set(v___x_6060_, 1, v_opts_6057_);
                leanh::lean_ctor_set(v___x_6060_, 2, v_currNamespace_6058_);
                leanh::lean_ctor_set(v___x_6060_, 3, v_openDecls_6059_);
                leanh::lean_inc_ref(v_parserState_5849_);
                leanh::lean_inc_ref(v_a_5854_);
                v___f_6061_ = leanh::lean_alloc_closure(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed as *mut core::ffi::c_void, 4, 3);
                leanh::lean_closure_set(v___f_6061_, 0, v_a_5854_);
                leanh::lean_closure_set(v___f_6061_, 1, v___x_6060_);
                leanh::lean_closure_set(v___f_6061_, 2, v_parserState_5849_);
                v___x_6062_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5;
                v___x_6063_ = leanh::lean_box(0);
                v___x_6064_ = lean_profileit(v___x_6062_, v_opts_6057_, v___f_6061_, v___x_6063_);
                v_snd_6065_ = leanh::lean_ctor_get(v___x_6064_, 1);
                leanh::lean_inc(v_snd_6065_);
                if leanh::lean_obj_tag(v_old_x3f_5848_) == 1 {
                    v_val_6066_ = leanh::lean_ctor_get(v_old_x3f_5848_, 0);
                    v_fst_6067_ = leanh::lean_ctor_get(v___x_6064_, 0);
                    leanh::lean_inc_n(v_fst_6067_, 2);
                    leanh::lean_dec(v___x_6064_);
                    v_fst_6068_ = leanh::lean_ctor_get(v_snd_6065_, 0);
                    leanh::lean_inc(v_fst_6068_);
                    v_snd_6069_ = leanh::lean_ctor_get(v_snd_6065_, 1);
                    leanh::lean_inc(v_snd_6069_);
                    leanh::lean_dec(v_snd_6065_);
                    v_pos_6070_ = leanh::lean_ctor_get(v_parserState_5849_, 0);
                    leanh::lean_inc(v_pos_6070_);
                    leanh::lean_dec_ref(v_parserState_5849_);
                    v_toSnapshot_6071_ = leanh::lean_ctor_get(v_val_6066_, 0);
                    v_stx_6072_ = leanh::lean_ctor_get(v_val_6066_, 1);
                    v_parserState_6073_ = leanh::lean_ctor_get(v_val_6066_, 2);
                    v_elabSnap_6074_ = leanh::lean_ctor_get(v_val_6066_, 3);
                    v_nextCmdSnap_x3f_6075_ = leanh::lean_ctor_get(v_val_6066_, 4);
                    leanh::lean_inc(v_stx_6072_);
                    v___x_6076_ = l_Lean_Syntax_eqWithInfo(v_fst_6067_, v_stx_6072_);
                    if v___x_6076_ == 0 {
                        if leanh::lean_obj_tag(v_nextCmdSnap_x3f_6075_) == 0 {
                            leanh::lean_inc(v_fst_6067_);
                            leanh::lean_inc_ref(v_opts_6057_);
                            leanh::lean_inc(v_fst_6068_);
                            v___y_6015_ = v_pos_6070_;
                            v___y_6016_ = v___x_6063_;
                            v___y_6017_ = v_fst_6068_;
                            v___y_6018_ = v_opts_6057_;
                            v___y_6019_ = v_fst_6067_;
                            v___y_6020_ = v_snd_6069_;
                            v___y_6021_ = v___x_6063_;
                            v___y_6022_ = v_opts_6057_;
                            v___y_6023_ = v_fst_6068_;
                            v___y_6024_ = v_fst_6067_;
                            state = 13;
                            continue;
                        } else {
                            v_val_6077_ = leanh::lean_ctor_get(v_nextCmdSnap_x3f_6075_, 0);
                            v___x_6078_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6;
                            leanh::lean_inc(v_val_6077_);
                            v___x_6079_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(
                                v___x_6078_,
                                v_val_6077_,
                            );
                            leanh::lean_inc(v_fst_6067_);
                            leanh::lean_inc_ref(v_opts_6057_);
                            leanh::lean_inc(v_fst_6068_);
                            v___y_6015_ = v_pos_6070_;
                            v___y_6016_ = v___x_6063_;
                            v___y_6017_ = v_fst_6068_;
                            v___y_6018_ = v_opts_6057_;
                            v___y_6019_ = v_fst_6067_;
                            v___y_6020_ = v_snd_6069_;
                            v___y_6021_ = v___x_6063_;
                            v___y_6022_ = v_opts_6057_;
                            v___y_6023_ = v_fst_6068_;
                            v___y_6024_ = v_fst_6067_;
                            state = 13;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_val_6066_);
                        leanh::lean_dec(v_pos_6070_);
                        leanh::lean_dec(v_snd_6069_);
                        leanh::lean_dec(v_fst_6067_);
                        leanh::lean_dec_ref_known(v_old_x3f_5848_, 1);
                        leanh::lean_dec_ref(v_opts_6057_);
                        leanh::lean_dec_ref(v_parseCancelTk_5853_);
                        leanh::lean_dec_ref(v_cmdState_5850_);
                        if leanh::lean_obj_tag(v_nextCmdSnap_x3f_6075_) == 1 {
                            leanh::lean_inc_ref(v_nextCmdSnap_x3f_6075_);
                            leanh::lean_inc_ref(v_elabSnap_6074_);
                            leanh::lean_inc_ref(v_parserState_6073_);
                            leanh::lean_inc(v_stx_6072_);
                            leanh::lean_inc_ref(v_toSnapshot_6071_);
                            leanh::lean_dec(v_val_6066_);
                            v_val_6080_ = leanh::lean_ctor_get(v_nextCmdSnap_x3f_6075_, 0);
                            leanh::lean_inc(v_val_6080_);
                            leanh::lean_dec_ref_known(v_nextCmdSnap_x3f_6075_, 1);
                            v_toSnapshot_5857_ = v_toSnapshot_6071_;
                            v_stx_5858_ = v_stx_6072_;
                            v_parserState_5859_ = v_parserState_6073_;
                            v_elabSnap_5860_ = v_elabSnap_6074_;
                            v_val_5861_ = v_val_6080_;
                            v_newParserState_5862_ = v_fst_6068_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_fst_6068_);
                            v___x_6081_ = lean_io_promise_resolve(v_val_6066_, v_prom_5851_);
                            leanh::lean_dec(v_prom_5851_);
                            return v___x_6081_;
                        }
                    }
                } else {
                    v_fst_6082_ = leanh::lean_ctor_get(v___x_6064_, 0);
                    leanh::lean_inc_n(v_fst_6082_, 2);
                    leanh::lean_dec(v___x_6064_);
                    v_fst_6083_ = leanh::lean_ctor_get(v_snd_6065_, 0);
                    leanh::lean_inc_n(v_fst_6083_, 2);
                    v_snd_6084_ = leanh::lean_ctor_get(v_snd_6065_, 1);
                    leanh::lean_inc(v_snd_6084_);
                    leanh::lean_dec(v_snd_6065_);
                    v_pos_6085_ = leanh::lean_ctor_get(v_parserState_5849_, 0);
                    leanh::lean_inc(v_pos_6085_);
                    leanh::lean_dec_ref(v_parserState_5849_);
                    leanh::lean_inc_ref(v_opts_6057_);
                    v___y_6015_ = v_pos_6085_;
                    v___y_6016_ = v___x_6063_;
                    v___y_6017_ = v_fst_6083_;
                    v___y_6018_ = v_opts_6057_;
                    v___y_6019_ = v_fst_6082_;
                    v___y_6020_ = v_snd_6084_;
                    v___y_6021_ = v___x_6063_;
                    v___y_6022_ = v_opts_6057_;
                    v___y_6023_ = v_fst_6083_;
                    v___y_6024_ = v_fst_6082_;
                    state = 13;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(
    mut v_oldResult_6102_: *mut leanh::LeanObject,
    mut v_newParserState_6103_: *mut leanh::LeanObject,
    mut v_val_6104_: *mut leanh::LeanObject,
    mut v_sync_6105_: u8,
    mut v_val_6106_: *mut leanh::LeanObject,
    mut v_a_6107_: *mut leanh::LeanObject,
    mut v_oldNext_6108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cmdState_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cmdState_6110_ = leanh::lean_ctor_get(v_oldResult_6102_, 1);
    leanh::lean_inc_ref(v_cmdState_6110_);
    leanh::lean_dec_ref(v_oldResult_6102_);
    v___x_6111_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6111_, 0, v_oldNext_6108_);
    v___x_6112_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(
        v___x_6111_,
        v_newParserState_6103_,
        v_cmdState_6110_,
        v_val_6104_,
        v_sync_6105_,
        v_val_6106_,
        v_a_6107_,
    );
    return v___x_6112_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6113_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_val_6114_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_fst_6115_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_val_6116_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_6117_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_snd_6118_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_6119_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_6120_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_fst_6121_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_val_6122_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_val_6123_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_val_6124_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_snd_6125_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_prom_6126_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___x_6127_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___f_6128_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___f_6129_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___f_6130_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_pos_6131_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_fst_6132_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_cmdState_6133_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_opts_6134_: *mut leanh::LeanObject = *_args.add(21);
    let mut v___x_6135_: *mut leanh::LeanObject = *_args.add(22);
    let mut v_old_x3f_6136_: *mut leanh::LeanObject = *_args.add(23);
    let mut v_parseCancelTk_6137_: *mut leanh::LeanObject = *_args.add(24);
    let mut v_next_x3f_6138_: *mut leanh::LeanObject = *_args.add(25);
    let mut v___y_6139_: *mut leanh::LeanObject = *_args.add(26);
    let mut v_val_45488__boxed_6140_: u8 = 0;
    let mut v___x_45491__boxed_6141_: u8 = 0;
    let mut v_res_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_45488__boxed_6140_ = (leanh::lean_unbox(v_val_6116_) as u8);
    v___x_45491__boxed_6141_ = (leanh::lean_unbox(v___x_6120_) as u8);
    v_res_6142_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(
        v___x_6113_,
        v_val_6114_,
        v_fst_6115_,
        v_val_45488__boxed_6140_,
        v_a_6117_,
        v_snd_6118_,
        v___x_6119_,
        v___x_45491__boxed_6141_,
        v_fst_6121_,
        v_val_6122_,
        v_val_6123_,
        v_val_6124_,
        v_snd_6125_,
        v_prom_6126_,
        v___x_6127_,
        v___f_6128_,
        v___f_6129_,
        v___f_6130_,
        v_pos_6131_,
        v_fst_6132_,
        v_cmdState_6133_,
        v_opts_6134_,
        v___x_6135_,
        v_old_x3f_6136_,
        v_parseCancelTk_6137_,
        v_next_x3f_6138_,
    );
    leanh::lean_dec_ref(v___x_6135_);
    leanh::lean_dec_ref(v_opts_6134_);
    leanh::lean_dec(v_prom_6126_);
    leanh::lean_dec(v_val_6123_);
    leanh::lean_dec_ref(v_a_6117_);
    leanh::lean_dec(v_val_6114_);
    return v_res_6142_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(
    mut v_old_x3f_6143_: *mut leanh::LeanObject,
    mut v_parserState_6144_: *mut leanh::LeanObject,
    mut v_cmdState_6145_: *mut leanh::LeanObject,
    mut v_prom_6146_: *mut leanh::LeanObject,
    mut v_sync_6147_: *mut leanh::LeanObject,
    mut v_parseCancelTk_6148_: *mut leanh::LeanObject,
    mut v_a_6149_: *mut leanh::LeanObject,
    mut v_a_6150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sync_boxed_6151_: u8 = 0;
    let mut v_res_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_6151_ = (leanh::lean_unbox(v_sync_6147_) as u8);
    v_res_6152_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(
        v_old_x3f_6143_,
        v_parserState_6144_,
        v_cmdState_6145_,
        v_prom_6146_,
        v_sync_boxed_6151_,
        v_parseCancelTk_6148_,
        v_a_6149_,
    );
    leanh::lean_dec_ref(v_a_6149_);
    return v_res_6152_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(
    mut v_as_6153_: *mut leanh::LeanObject,
    mut v_i_6154_: usize,
    mut v_stop_6155_: usize,
    mut v_b_6156_: *mut leanh::LeanObject,
    mut v___y_6157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_6153_, v_i_6154_, v_stop_6155_, v_b_6156_);
    return v___x_6159_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___boxed(
    mut v_as_6160_: *mut leanh::LeanObject,
    mut v_i_6161_: *mut leanh::LeanObject,
    mut v_stop_6162_: *mut leanh::LeanObject,
    mut v_b_6163_: *mut leanh::LeanObject,
    mut v___y_6164_: *mut leanh::LeanObject,
    mut v___y_6165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6166_: usize = 0;
    let mut v_stop_boxed_6167_: usize = 0;
    let mut v_res_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6166_ = leanh::lean_unbox_usize(v_i_6161_);
    leanh::lean_dec(v_i_6161_);
    v_stop_boxed_6167_ = leanh::lean_unbox_usize(v_stop_6162_);
    leanh::lean_dec(v_stop_6162_);
    v_res_6168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(v_as_6160_, v_i_boxed_6166_, v_stop_boxed_6167_, v_b_6163_, v___y_6164_);
    leanh::lean_dec_ref(v___y_6164_);
    leanh::lean_dec_ref(v_as_6160_);
    return v_res_6168_;
}
pub unsafe fn l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(
    mut v_opts_6169_: *mut leanh::LeanObject,
    mut v_opt_6170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6178_: u8 = 0;
    let mut v_v_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6184_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_6171_ = leanh::lean_ctor_get(v_opt_6170_, 0);
                v_map_6172_ = leanh::lean_ctor_get(v_opts_6169_, 0);
                v___x_6173_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6172_, v_name_6171_);
                if leanh::lean_obj_tag(v___x_6173_) == 0 {
                    v___x_6174_ = leanh::lean_box(0);
                    return v___x_6174_;
                } else {
                    v_val_6175_ = leanh::lean_ctor_get(v___x_6173_, 0);
                    v_isSharedCheck_6184_ = (!leanh::lean_is_exclusive(v___x_6173_)) as u8;
                    if v_isSharedCheck_6184_ == 0 {
                        v___x_6177_ = v___x_6173_;
                        v_isShared_6178_ = v_isSharedCheck_6184_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6175_);
                        leanh::lean_dec(v___x_6173_);
                        v___x_6177_ = leanh::lean_box(0);
                        v_isShared_6178_ = v_isSharedCheck_6184_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_val_6175_) == 0 {
                    v_v_6179_ = leanh::lean_ctor_get(v_val_6175_, 0);
                    leanh::lean_inc_ref(v_v_6179_);
                    leanh::lean_dec_ref_known(v_val_6175_, 1);
                    if v_isShared_6178_ == 0 {
                        leanh::lean_ctor_set(v___x_6177_, 0, v_v_6179_);
                        v___x_6181_ = v___x_6177_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6182_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6182_, 0, v_v_6179_);
                        v___x_6181_ = v_reuseFailAlloc_6182_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6177_);
                    leanh::lean_dec(v_val_6175_);
                    v___x_6183_ = leanh::lean_box(0);
                    return v___x_6183_;
                }
            }
            2 => {
                return v___x_6181_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(
    mut v_opts_6185_: *mut leanh::LeanObject,
    mut v_opt_6186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6187_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_6185_, v_opt_6186_);
    leanh::lean_dec_ref(v_opt_6186_);
    leanh::lean_dec_ref(v_opts_6185_);
    return v_res_6187_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(
    mut v___x_6188_: *mut leanh::LeanObject,
    mut v_x_6189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6190_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_6188_);
    v___x_6191_ = leanh::lean_box(0);
    v___x_6192_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6192_, 0, v_x_6189_);
    leanh::lean_ctor_set(v___x_6192_, 1, v___x_6190_);
    leanh::lean_ctor_set(v___x_6192_, 2, v___x_6191_);
    return v___x_6192_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6198_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2;
    v___x_6199_ = l_Array_toPArray_x27___redArg(v___x_6198_);
    return v___x_6199_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(
    mut v_a_6200_: *mut leanh::LeanObject,
    mut v_a_6201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6207_: u8 = 0;
    let mut v___x_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6200_) == 0 {
                    v___x_6202_ = l_List_reverse___redArg(v_a_6201_);
                    return v___x_6202_;
                } else {
                    v_head_6203_ = leanh::lean_ctor_get(v_a_6200_, 0);
                    v_tail_6204_ = leanh::lean_ctor_get(v_a_6200_, 1);
                    v_isSharedCheck_6217_ = (!leanh::lean_is_exclusive(v_a_6200_)) as u8;
                    if v_isSharedCheck_6217_ == 0 {
                        v___x_6206_ = v_a_6200_;
                        v_isShared_6207_ = v_isSharedCheck_6217_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6204_);
                        leanh::lean_inc(v_head_6203_);
                        leanh::lean_dec(v_a_6200_);
                        v___x_6206_ = leanh::lean_box(0);
                        v_isShared_6207_ = v_isSharedCheck_6217_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6208_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1;
                v___x_6209_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6209_, 0, v___x_6208_);
                leanh::lean_ctor_set(v___x_6209_, 1, v_head_6203_);
                v___x_6210_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6210_, 0, v___x_6209_);
                v___x_6211_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once), _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
                v___x_6212_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6212_, 0, v___x_6210_);
                leanh::lean_ctor_set(v___x_6212_, 1, v___x_6211_);
                if v_isShared_6207_ == 0 {
                    leanh::lean_ctor_set(v___x_6206_, 1, v_a_6201_);
                    leanh::lean_ctor_set(v___x_6206_, 0, v___x_6212_);
                    v___x_6214_ = v___x_6206_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6216_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6216_, 0, v___x_6212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6216_, 1, v_a_6201_);
                    v___x_6214_ = v_reuseFailAlloc_6216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6200_ = v_tail_6204_;
                v_a_6201_ = v___x_6214_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6()
-> f64 {
    let mut v___x_6228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: f64 = 0.0;
    v___x_6228_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_6229_ = lean_float_of_nat(v___x_6228_);
    return v___x_6229_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6236_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10;
    v___x_6237_ = l_Lean_MessageData_ofFormat(v___x_6236_);
    return v___x_6237_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(
    mut v_setupImports_6238_: *mut leanh::LeanObject,
    mut v_stx_6239_: *mut leanh::LeanObject,
    mut v_origStx_6240_: *mut leanh::LeanObject,
    mut v_toProcessingContext_6241_: *mut leanh::LeanObject,
    mut v___x_6242_: *mut leanh::LeanObject,
    mut v_fileMap_6243_: *mut leanh::LeanObject,
    mut v_parserState_6244_: *mut leanh::LeanObject,
    mut v_a_6245_: *mut leanh::LeanObject,
    mut v___x_6246_: *mut leanh::LeanObject,
    mut v___x_6247_: *mut leanh::LeanObject,
    mut v___y_6248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toProcessingContext_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6255_: u8 = 0;
    let mut v_a_6256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6263_: u8 = 0;
    let mut v___x_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModuleName_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_x3f_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_6267_: u8 = 0;
    let mut v_imports_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_6269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trustLevel_6270_: u32 = 0;
    let mut v_importArts_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_6272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: u8 = 0;
    let mut v___x_6277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6283_: u8 = 0;
    let mut v_fst_6284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6288_: u8 = 0;
    let mut v___x_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: u8 = 0;
    let mut v___y_6293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6326_: u8 = 0;
    let mut v___x_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: usize = 0;
    let mut v___x_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: u64 = 0;
    let mut v___x_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: u8 = 0;
    let mut v___x_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6388_: u8 = 0;
    let mut v_unused_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6394_: u8 = 0;
    let mut v___x_6396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6398_: u8 = 0;
    let mut v___x_6399_: f64 = 0.0;
    let mut v___x_6400_: f64 = 0.0;
    let mut v___x_6401_: f64 = 0.0;
    let mut v___x_6402_: f64 = 0.0;
    let mut v___x_6403_: f64 = 0.0;
    let mut v___x_6405_: u64 = 0;
    let mut v___x_6406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: u8 = 0;
    let mut v___x_6424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: u64 = 0;
    let mut v___x_6439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: usize = 0;
    let mut v___x_6443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6451_: u8 = 0;
    let mut v_isSharedCheck_6452_: u8 = 0;
    let mut v_a_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6456_: u8 = 0;
    let mut v___x_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6460_: u8 = 0;
    let mut v_reuseFailAlloc_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6462_: u8 = 0;
    let mut v_isSharedCheck_6463_: u8 = 0;
    let mut v_a_6464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6467_: u8 = 0;
    let mut v___x_6469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toProcessingContext_6250_ = leanh::lean_ctor_get(v___y_6248_, 0);
                leanh::lean_inc_ref(v_toProcessingContext_6250_);
                leanh::lean_inc(v_stx_6239_);
                v___x_6251_ = leanh::lean_apply_3(
                    v_setupImports_6238_,
                    v_stx_6239_,
                    v_toProcessingContext_6250_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_6251_) == 0 {
                    v_a_6252_ = leanh::lean_ctor_get(v___x_6251_, 0);
                    v_isSharedCheck_6463_ = (!leanh::lean_is_exclusive(v___x_6251_)) as u8;
                    if v_isSharedCheck_6463_ == 0 {
                        v___x_6254_ = v___x_6251_;
                        v_isShared_6255_ = v_isSharedCheck_6463_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6252_);
                        leanh::lean_dec(v___x_6251_);
                        v___x_6254_ = leanh::lean_box(0);
                        v_isShared_6255_ = v_isSharedCheck_6463_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_6247_);
                    leanh::lean_dec(v___x_6246_);
                    leanh::lean_dec_ref(v_parserState_6244_);
                    leanh::lean_dec_ref(v_fileMap_6243_);
                    leanh::lean_dec(v___x_6242_);
                    leanh::lean_dec_ref(v_toProcessingContext_6241_);
                    leanh::lean_dec(v_origStx_6240_);
                    leanh::lean_dec(v_stx_6239_);
                    v_a_6464_ = leanh::lean_ctor_get(v___x_6251_, 0);
                    v_isSharedCheck_6471_ = (!leanh::lean_is_exclusive(v___x_6251_)) as u8;
                    if v_isSharedCheck_6471_ == 0 {
                        v___x_6466_ = v___x_6251_;
                        v_isShared_6467_ = v_isSharedCheck_6471_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6464_);
                        leanh::lean_dec(v___x_6251_);
                        v___x_6466_ = leanh::lean_box(0);
                        v_isShared_6467_ = v_isSharedCheck_6471_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6252_) == 0 {
                    leanh::lean_dec_ref(v___x_6247_);
                    leanh::lean_dec(v___x_6246_);
                    leanh::lean_dec_ref(v_parserState_6244_);
                    leanh::lean_dec_ref(v_fileMap_6243_);
                    leanh::lean_dec(v___x_6242_);
                    leanh::lean_dec_ref(v_toProcessingContext_6241_);
                    leanh::lean_dec(v_origStx_6240_);
                    leanh::lean_dec(v_stx_6239_);
                    v_a_6256_ = leanh::lean_ctor_get(v_a_6252_, 0);
                    leanh::lean_inc(v_a_6256_);
                    leanh::lean_dec_ref_known(v_a_6252_, 1);
                    if v_isShared_6255_ == 0 {
                        leanh::lean_ctor_set(v___x_6254_, 0, v_a_6256_);
                        v___x_6258_ = v___x_6254_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6259_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6259_, 0, v_a_6256_);
                        v___x_6258_ = v_reuseFailAlloc_6259_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6260_ = leanh::lean_ctor_get(v_a_6252_, 0);
                    v_isSharedCheck_6462_ = (!leanh::lean_is_exclusive(v_a_6252_)) as u8;
                    if v_isSharedCheck_6462_ == 0 {
                        v___x_6262_ = v_a_6252_;
                        v_isShared_6263_ = v_isSharedCheck_6462_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6260_);
                        leanh::lean_dec(v_a_6252_);
                        v___x_6262_ = leanh::lean_box(0);
                        v_isShared_6263_ = v_isSharedCheck_6462_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6258_;
            }
            3 => {
                v___x_6264_ = lean_io_mono_nanos_now();
                v_mainModuleName_6265_ = leanh::lean_ctor_get(v_a_6260_, 0);
                leanh::lean_inc(v_mainModuleName_6265_);
                v_package_x3f_6266_ = leanh::lean_ctor_get(v_a_6260_, 1);
                leanh::lean_inc(v_package_x3f_6266_);
                v_isModule_6267_ = leanh::lean_ctor_get_uint8(
                    v_a_6260_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6 + 4) as u32,
                );
                v_imports_6268_ = leanh::lean_ctor_get(v_a_6260_, 2);
                leanh::lean_inc_ref(v_imports_6268_);
                v_opts_6269_ = leanh::lean_ctor_get(v_a_6260_, 3);
                leanh::lean_inc_ref(v_opts_6269_);
                v_trustLevel_6270_ = leanh::lean_ctor_get_uint32(
                    v_a_6260_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_importArts_6271_ = leanh::lean_ctor_get(v_a_6260_, 4);
                leanh::lean_inc(v_importArts_6271_);
                v_plugins_6272_ = leanh::lean_ctor_get(v_a_6260_, 5);
                leanh::lean_inc_ref(v_plugins_6272_);
                leanh::lean_dec(v_a_6260_);
                v___x_6273_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_6239_);
                v___x_6274_ = l_Lean_MessageLog_empty;
                v___x_6275_ = 1;
                leanh::lean_inc(v_stx_6239_);
                if v_isShared_6263_ == 0 {
                    leanh::lean_ctor_set(v___x_6262_, 0, v_stx_6239_);
                    v___x_6277_ = v___x_6262_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6461_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6461_, 0, v_stx_6239_);
                    v___x_6277_ = v_reuseFailAlloc_6461_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6278_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6278_, 0, v_origStx_6240_);
                leanh::lean_inc_ref(v___x_6277_);
                leanh::lean_inc_ref(v_opts_6269_);
                v___x_6279_ = l_Lean_Elab_processHeaderCore(
                    v___x_6273_,
                    v_imports_6268_,
                    v_isModule_6267_,
                    v_opts_6269_,
                    v___x_6274_,
                    v_toProcessingContext_6241_,
                    v_trustLevel_6270_,
                    v_plugins_6272_,
                    v___x_6275_,
                    v_mainModuleName_6265_,
                    v_package_x3f_6266_,
                    v_importArts_6271_,
                    v___x_6277_,
                    v___x_6278_,
                );
                leanh::lean_dec(v___x_6273_);
                if leanh::lean_obj_tag(v___x_6279_) == 0 {
                    v_a_6280_ = leanh::lean_ctor_get(v___x_6279_, 0);
                    v_isSharedCheck_6452_ = (!leanh::lean_is_exclusive(v___x_6279_)) as u8;
                    if v_isSharedCheck_6452_ == 0 {
                        v___x_6282_ = v___x_6279_;
                        v_isShared_6283_ = v_isSharedCheck_6452_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6280_);
                        leanh::lean_dec(v___x_6279_);
                        v___x_6282_ = leanh::lean_box(0);
                        v_isShared_6283_ = v_isSharedCheck_6452_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_6277_);
                    leanh::lean_dec_ref(v_opts_6269_);
                    leanh::lean_dec(v___x_6264_);
                    leanh::lean_del_object(v___x_6254_);
                    leanh::lean_dec_ref(v___x_6247_);
                    leanh::lean_dec(v___x_6246_);
                    leanh::lean_dec_ref(v_parserState_6244_);
                    leanh::lean_dec_ref(v_fileMap_6243_);
                    leanh::lean_dec(v___x_6242_);
                    leanh::lean_dec(v_stx_6239_);
                    v_a_6453_ = leanh::lean_ctor_get(v___x_6279_, 0);
                    v_isSharedCheck_6460_ = (!leanh::lean_is_exclusive(v___x_6279_)) as u8;
                    if v_isSharedCheck_6460_ == 0 {
                        v___x_6455_ = v___x_6279_;
                        v_isShared_6456_ = v_isSharedCheck_6460_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6453_);
                        leanh::lean_dec(v___x_6279_);
                        v___x_6455_ = leanh::lean_box(0);
                        v_isShared_6456_ = v_isSharedCheck_6460_;
                        state = 17;
                        continue;
                    }
                }
            }
            5 => {
                v_fst_6284_ = leanh::lean_ctor_get(v_a_6280_, 0);
                v_snd_6285_ = leanh::lean_ctor_get(v_a_6280_, 1);
                v_isSharedCheck_6451_ = (!leanh::lean_is_exclusive(v_a_6280_)) as u8;
                if v_isSharedCheck_6451_ == 0 {
                    v___x_6287_ = v_a_6280_;
                    v_isShared_6288_ = v_isSharedCheck_6451_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6285_);
                    leanh::lean_inc(v_fst_6284_);
                    leanh::lean_dec(v_a_6280_);
                    v___x_6287_ = leanh::lean_box(0);
                    v_isShared_6288_ = v_isSharedCheck_6451_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6289_ = lean_io_mono_nanos_now();
                leanh::lean_inc(v_snd_6285_);
                v___x_6290_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_6285_);
                v___x_6291_ = l_Lean_MessageLog_hasErrors(v_snd_6285_);
                if v___x_6291_ == 0 {
                    leanh::lean_del_object(v___x_6254_);
                    leanh::lean_dec_ref(v___x_6247_);
                    v___x_6399_ = lean_float_of_nat(v___x_6264_);
                    v___x_6400_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
                    v___x_6401_ = lean_float_div(v___x_6399_, v___x_6400_);
                    v___x_6402_ = lean_float_of_nat(v___x_6289_);
                    v___x_6403_ = lean_float_div(v___x_6402_, v___x_6400_);
                    v___x_6420_ = l_Lean_trace_profiler_output;
                    v___x_6421_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_6269_, v___x_6420_);
                    if leanh::lean_obj_tag(v___x_6421_) == 0 {
                        v___x_6422_ = l_Lean_trace_profiler_serve;
                        v___x_6423_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_6269_, v___x_6422_);
                        if v___x_6423_ == 0 {
                            v___x_6424_ = l_Lean_instInhabitedTraceState_default;
                            v_traceState_6307_ = v___x_6424_;
                            state = 9;
                            continue;
                        } else {
                            state = 15;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_6421_, 1);
                        state = 15;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_6289_);
                    leanh::lean_del_object(v___x_6287_);
                    leanh::lean_dec(v_snd_6285_);
                    leanh::lean_dec(v_fst_6284_);
                    leanh::lean_del_object(v___x_6282_);
                    leanh::lean_dec_ref(v___x_6277_);
                    leanh::lean_dec_ref(v_opts_6269_);
                    leanh::lean_dec(v___x_6264_);
                    leanh::lean_dec(v___x_6246_);
                    leanh::lean_dec_ref(v_parserState_6244_);
                    leanh::lean_dec_ref(v_fileMap_6243_);
                    leanh::lean_dec(v_stx_6239_);
                    v___x_6425_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2;
                    v___x_6426_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4;
                    v___x_6427_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6;
                    leanh::lean_inc_n(v___x_6242_, 2);
                    v___x_6428_ = l_Lean_Name_num___override(v___x_6427_, v___x_6242_);
                    v___x_6429_ = l_Lean_Name_str___override(v___x_6428_, v___x_6425_);
                    v___x_6430_ = l_Lean_Name_str___override(v___x_6429_, v___x_6426_);
                    v___x_6431_ = l_Lean_Name_str___override(v___x_6430_, v___x_6425_);
                    v___x_6432_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0;
                    v___x_6433_ = l_Lean_Name_str___override(v___x_6431_, v___x_6432_);
                    v___x_6434_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5;
                    v___x_6435_ = l_Lean_Name_str___override(v___x_6433_, v___x_6434_);
                    v___x_6436_ = l_Lean_Name_toString(v___x_6435_, v___x_6275_);
                    v___x_6437_ = leanh::lean_box(0);
                    v___x_6438_ = 0u64;
                    v___x_6439_ = leanh::lean_unsigned_to_nat(32);
                    v___x_6440_ = lean_mk_empty_array_with_capacity(v___x_6439_);
                    v___x_6441_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
                    v___x_6442_ = 5usize;
                    v___x_6443_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v___x_6443_, 0, v___x_6441_);
                    leanh::lean_ctor_set(v___x_6443_, 1, v___x_6440_);
                    leanh::lean_ctor_set(v___x_6443_, 2, v___x_6242_);
                    leanh::lean_ctor_set(v___x_6443_, 3, v___x_6242_);
                    leanh::lean_ctor_set_usize(v___x_6443_, 4, v___x_6442_);
                    v___x_6444_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v___x_6444_, 0, v___x_6443_);
                    leanh::lean_ctor_set_uint64(
                        v___x_6444_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_6438_,
                    );
                    v___x_6445_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v___x_6445_, 0, v___x_6436_);
                    leanh::lean_ctor_set(v___x_6445_, 1, v___x_6290_);
                    leanh::lean_ctor_set(v___x_6445_, 2, v___x_6437_);
                    leanh::lean_ctor_set(v___x_6445_, 3, v___x_6444_);
                    leanh::lean_ctor_set_uint8(
                        v___x_6445_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v___x_6291_,
                    );
                    v___x_6446_ =
                        l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_6247_);
                    v___x_6447_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_6447_, 0, v___x_6445_);
                    leanh::lean_ctor_set(v___x_6447_, 1, v___x_6446_);
                    leanh::lean_ctor_set(v___x_6447_, 2, v___x_6437_);
                    if v_isShared_6255_ == 0 {
                        leanh::lean_ctor_set(v___x_6254_, 0, v___x_6447_);
                        v___x_6449_ = v___x_6254_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_6450_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6450_, 0, v___x_6447_);
                        v___x_6449_ = v_reuseFailAlloc_6450_;
                        state = 16;
                        continue;
                    }
                }
            }
            7 => {
                v___x_6299_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6299_, 0, v___y_6298_);
                v___x_6300_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_6300_, 0, v___y_6296_);
                leanh::lean_ctor_set(v___x_6300_, 1, v___x_6290_);
                leanh::lean_ctor_set(v___x_6300_, 2, v___x_6299_);
                leanh::lean_ctor_set(v___x_6300_, 3, v___y_6295_);
                leanh::lean_ctor_set_uint8(
                    v___x_6300_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_6291_,
                );
                v___x_6301_ =
                    l_Lean_Language_SnapshotTask_finished___redArg(v___y_6297_, v___x_6300_);
                v___x_6302_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6302_, 0, v___y_6294_);
                leanh::lean_ctor_set(v___x_6302_, 1, v___x_6301_);
                leanh::lean_ctor_set(v___x_6302_, 2, v___y_6293_);
                if v_isShared_6283_ == 0 {
                    leanh::lean_ctor_set(v___x_6282_, 0, v___x_6302_);
                    v___x_6304_ = v___x_6282_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6305_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6305_, 0, v___x_6302_);
                    v___x_6304_ = v_reuseFailAlloc_6305_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6304_;
            }
            9 => {
                v___x_6308_ = l_Lean_Language_Lean_reparseOptions(v_opts_6269_);
                if leanh::lean_obj_tag(v___x_6308_) == 0 {
                    v_a_6309_ = leanh::lean_ctor_get(v___x_6308_, 0);
                    leanh::lean_inc(v_a_6309_);
                    leanh::lean_dec_ref_known(v___x_6308_, 1);
                    v___x_6310_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
                    leanh::lean_inc_n(v___x_6242_, 4);
                    v___x_6311_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v___x_6311_, 0, v___x_6242_);
                    leanh::lean_ctor_set(v___x_6311_, 1, v___x_6242_);
                    leanh::lean_ctor_set(v___x_6311_, 2, v___x_6242_);
                    leanh::lean_ctor_set(v___x_6311_, 3, v___x_6242_);
                    leanh::lean_ctor_set(v___x_6311_, 4, v___x_6310_);
                    leanh::lean_ctor_set(v___x_6311_, 5, v___x_6310_);
                    leanh::lean_ctor_set(v___x_6311_, 6, v___x_6310_);
                    leanh::lean_ctor_set(v___x_6311_, 7, v___x_6310_);
                    leanh::lean_ctor_set(v___x_6311_, 8, v___x_6310_);
                    leanh::lean_ctor_set(v___x_6311_, 9, v___x_6310_);
                    v___x_6312_ = lean_io_promise_new();
                    v___x_6313_ = l_IO_CancelToken_new();
                    leanh::lean_inc(v_fst_6284_);
                    v___x_6314_ = l_Lean_Elab_Command_mkState(v_fst_6284_, v_snd_6285_, v_a_6309_);
                    v_env_6315_ = leanh::lean_ctor_get(v___x_6314_, 0);
                    v_messages_6316_ = leanh::lean_ctor_get(v___x_6314_, 1);
                    v_scopes_6317_ = leanh::lean_ctor_get(v___x_6314_, 2);
                    v_usedQuotCtxts_6318_ = leanh::lean_ctor_get(v___x_6314_, 3);
                    v_nextMacroScope_6319_ = leanh::lean_ctor_get(v___x_6314_, 4);
                    v_maxRecDepth_6320_ = leanh::lean_ctor_get(v___x_6314_, 5);
                    v_ngen_6321_ = leanh::lean_ctor_get(v___x_6314_, 6);
                    v_auxDeclNGen_6322_ = leanh::lean_ctor_get(v___x_6314_, 7);
                    v_snapshotTasks_6323_ = leanh::lean_ctor_get(v___x_6314_, 10);
                    v_isSharedCheck_6388_ = (!leanh::lean_is_exclusive(v___x_6314_)) as u8;
                    if v_isSharedCheck_6388_ == 0 {
                        v_unused_6389_ = leanh::lean_ctor_get(v___x_6314_, 9);
                        leanh::lean_dec(v_unused_6389_);
                        v_unused_6390_ = leanh::lean_ctor_get(v___x_6314_, 8);
                        leanh::lean_dec(v_unused_6390_);
                        v___x_6325_ = v___x_6314_;
                        v_isShared_6326_ = v_isSharedCheck_6388_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_6323_);
                        leanh::lean_inc(v_auxDeclNGen_6322_);
                        leanh::lean_inc(v_ngen_6321_);
                        leanh::lean_inc(v_maxRecDepth_6320_);
                        leanh::lean_inc(v_nextMacroScope_6319_);
                        leanh::lean_inc(v_usedQuotCtxts_6318_);
                        leanh::lean_inc(v_scopes_6317_);
                        leanh::lean_inc(v_messages_6316_);
                        leanh::lean_inc(v_env_6315_);
                        leanh::lean_dec(v___x_6314_);
                        v___x_6325_ = leanh::lean_box(0);
                        v_isShared_6326_ = v_isSharedCheck_6388_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_traceState_6307_);
                    leanh::lean_dec_ref(v___x_6290_);
                    leanh::lean_del_object(v___x_6287_);
                    leanh::lean_dec(v_snd_6285_);
                    leanh::lean_dec(v_fst_6284_);
                    leanh::lean_del_object(v___x_6282_);
                    leanh::lean_dec_ref(v___x_6277_);
                    leanh::lean_dec(v___x_6246_);
                    leanh::lean_dec_ref(v_parserState_6244_);
                    leanh::lean_dec_ref(v_fileMap_6243_);
                    leanh::lean_dec(v___x_6242_);
                    leanh::lean_dec(v_stx_6239_);
                    v_a_6391_ = leanh::lean_ctor_get(v___x_6308_, 0);
                    v_isSharedCheck_6398_ = (!leanh::lean_is_exclusive(v___x_6308_)) as u8;
                    if v_isSharedCheck_6398_ == 0 {
                        v___x_6393_ = v___x_6308_;
                        v_isShared_6394_ = v_isSharedCheck_6398_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6391_);
                        leanh::lean_dec(v___x_6308_);
                        v___x_6393_ = leanh::lean_box(0);
                        v_isShared_6394_ = v_isSharedCheck_6398_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                v___x_6327_ = leanh::lean_box(0);
                v___x_6328_ = l_Lean_Options_empty;
                v___x_6329_ = leanh::lean_box(0);
                v___x_6330_ = leanh::lean_box(0);
                v___x_6331_ = leanh::lean_unsigned_to_nat(1);
                v___x_6332_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2;
                v___x_6333_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                leanh::lean_ctor_set(v___x_6333_, 0, v_fst_6284_);
                leanh::lean_ctor_set(v___x_6333_, 1, v___x_6327_);
                leanh::lean_ctor_set(v___x_6333_, 2, v_fileMap_6243_);
                leanh::lean_ctor_set(v___x_6333_, 3, v___x_6311_);
                leanh::lean_ctor_set(v___x_6333_, 4, v___x_6328_);
                leanh::lean_ctor_set(v___x_6333_, 5, v___x_6329_);
                leanh::lean_ctor_set(v___x_6333_, 6, v___x_6330_);
                leanh::lean_ctor_set(v___x_6333_, 7, v___x_6332_);
                v___x_6334_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6334_, 0, v___x_6333_);
                v___x_6335_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4;
                leanh::lean_inc(v_stx_6239_);
                if v_isShared_6288_ == 0 {
                    leanh::lean_ctor_set(v___x_6287_, 1, v_stx_6239_);
                    leanh::lean_ctor_set(v___x_6287_, 0, v___x_6335_);
                    v___x_6337_ = v___x_6287_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6387_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6387_, 0, v___x_6335_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6387_, 1, v_stx_6239_);
                    v___x_6337_ = v_reuseFailAlloc_6387_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_6338_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6338_, 0, v___x_6337_);
                v___x_6339_ = leanh::lean_unsigned_to_nat(2);
                v___x_6340_ = l_Lean_Syntax_getArg(v_stx_6239_, v___x_6339_);
                leanh::lean_dec(v_stx_6239_);
                v___x_6341_ = l_Lean_Syntax_getArgs(v___x_6340_);
                leanh::lean_dec(v___x_6340_);
                v___x_6342_ = lean_array_to_list(v___x_6341_);
                v___x_6343_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_6342_, v___x_6330_);
                v___x_6344_ = l_List_toPArray_x27___redArg(v___x_6343_);
                v___x_6345_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6345_, 0, v___x_6338_);
                leanh::lean_ctor_set(v___x_6345_, 1, v___x_6344_);
                v___x_6346_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6346_, 0, v___x_6334_);
                leanh::lean_ctor_set(v___x_6346_, 1, v___x_6345_);
                v___x_6347_ = lean_mk_empty_array_with_capacity(v___x_6331_);
                v___x_6348_ = lean_array_push(v___x_6347_, v___x_6346_);
                v___x_6349_ = l_Array_toPArray_x27___redArg(v___x_6348_);
                leanh::lean_dec_ref(v___x_6348_);
                leanh::lean_inc_ref(v___x_6349_);
                v___x_6350_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_6350_, 0, v___x_6310_);
                leanh::lean_ctor_set(v___x_6350_, 1, v___x_6310_);
                leanh::lean_ctor_set(v___x_6350_, 2, v___x_6349_);
                leanh::lean_ctor_set_uint8(
                    v___x_6350_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_6275_,
                );
                if v_isShared_6326_ == 0 {
                    leanh::lean_ctor_set(v___x_6325_, 9, v_traceState_6307_);
                    leanh::lean_ctor_set(v___x_6325_, 8, v___x_6350_);
                    v___x_6352_ = v___x_6325_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6386_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 0, v_env_6315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 1, v_messages_6316_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 2, v_scopes_6317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 3, v_usedQuotCtxts_6318_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 4, v_nextMacroScope_6319_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 5, v_maxRecDepth_6320_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 6, v_ngen_6321_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 7, v_auxDeclNGen_6322_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 8, v___x_6350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 9, v_traceState_6307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6386_, 10, v_snapshotTasks_6323_);
                    v___x_6352_ = v_reuseFailAlloc_6386_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                leanh::lean_inc_ref(v___x_6313_);
                leanh::lean_inc(v___x_6312_);
                leanh::lean_inc_ref(v___x_6352_);
                v___x_6353_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(
                    v___x_6327_,
                    v_parserState_6244_,
                    v___x_6352_,
                    v___x_6312_,
                    v___x_6275_,
                    v___x_6313_,
                    v_a_6245_,
                );
                v___x_6354_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2;
                v___x_6355_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4;
                v___x_6356_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6;
                leanh::lean_inc_n(v___x_6242_, 3);
                v___x_6357_ = l_Lean_Name_num___override(v___x_6356_, v___x_6242_);
                v___x_6358_ = leanh::lean_unsigned_to_nat(32);
                v___x_6359_ = lean_mk_empty_array_with_capacity(v___x_6358_);
                v___x_6360_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
                v___x_6361_ = 5usize;
                v___x_6362_ =
                    leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                leanh::lean_ctor_set(v___x_6362_, 0, v___x_6360_);
                leanh::lean_ctor_set(v___x_6362_, 1, v___x_6359_);
                leanh::lean_ctor_set(v___x_6362_, 2, v___x_6242_);
                leanh::lean_ctor_set(v___x_6362_, 3, v___x_6242_);
                leanh::lean_ctor_set_usize(v___x_6362_, 4, v___x_6361_);
                v_size_6363_ = leanh::lean_ctor_get(v___x_6349_, 2);
                leanh::lean_inc(v_size_6363_);
                v___x_6364_ = l_Lean_Name_str___override(v___x_6357_, v___x_6354_);
                v___x_6365_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_6246_);
                v___x_6366_ = l_Lean_Name_str___override(v___x_6364_, v___x_6355_);
                v___x_6367_ = l_Lean_Name_str___override(v___x_6366_, v___x_6354_);
                v___x_6368_ =
                    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0;
                v___x_6369_ = l_Lean_Name_str___override(v___x_6367_, v___x_6368_);
                v___x_6370_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5;
                v___x_6371_ = l_Lean_Name_str___override(v___x_6369_, v___x_6370_);
                v___x_6372_ = l_Lean_Name_toString(v___x_6371_, v___x_6275_);
                v___x_6373_ = l_Lean_Language_Snapshot_Diagnostics_empty;
                v___x_6374_ = 0u64;
                v___x_6375_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_6375_, 0, v___x_6362_);
                leanh::lean_ctor_set_uint64(
                    v___x_6375_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_6374_,
                );
                v___x_6376_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6376_, 0, v___x_6313_);
                v___x_6377_ = l_IO_Promise_result_x21___redArg(v___x_6312_);
                leanh::lean_dec(v___x_6312_);
                v___x_6378_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_6378_, 0, v___x_6246_);
                leanh::lean_ctor_set(v___x_6378_, 1, v___x_6365_);
                leanh::lean_ctor_set(v___x_6378_, 2, v___x_6376_);
                leanh::lean_ctor_set(v___x_6378_, 3, v___x_6377_);
                v___x_6379_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6379_, 0, v___x_6352_);
                leanh::lean_ctor_set(v___x_6379_, 1, v___x_6378_);
                v___x_6380_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6380_, 0, v___x_6379_);
                leanh::lean_inc_ref(v___x_6375_);
                leanh::lean_inc_ref(v___x_6372_);
                v___x_6381_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_6381_, 0, v___x_6372_);
                leanh::lean_ctor_set(v___x_6381_, 1, v___x_6373_);
                leanh::lean_ctor_set(v___x_6381_, 2, v___x_6327_);
                leanh::lean_ctor_set(v___x_6381_, 3, v___x_6375_);
                leanh::lean_ctor_set_uint8(
                    v___x_6381_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_6291_,
                );
                v___x_6382_ = l_Lean_Elab_instInhabitedInfoTree_default;
                v___x_6383_ = lean_nat_dec_lt(v___x_6242_, v_size_6363_);
                leanh::lean_dec(v_size_6363_);
                if v___x_6383_ == 0 {
                    leanh::lean_dec_ref(v___x_6349_);
                    leanh::lean_dec(v___x_6242_);
                    v___x_6384_ = l_outOfBounds___redArg(v___x_6382_);
                    v___y_6293_ = v___x_6380_;
                    v___y_6294_ = v___x_6381_;
                    v___y_6295_ = v___x_6375_;
                    v___y_6296_ = v___x_6372_;
                    v___y_6297_ = v___x_6277_;
                    v___y_6298_ = v___x_6384_;
                    state = 7;
                    continue;
                } else {
                    v___x_6385_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_6382_,
                        v___x_6349_,
                        v___x_6242_,
                    );
                    leanh::lean_dec(v___x_6242_);
                    leanh::lean_dec_ref(v___x_6349_);
                    v___y_6293_ = v___x_6380_;
                    v___y_6294_ = v___x_6381_;
                    v___y_6295_ = v___x_6375_;
                    v___y_6296_ = v___x_6372_;
                    v___y_6297_ = v___x_6277_;
                    v___y_6298_ = v___x_6385_;
                    state = 7;
                    continue;
                }
            }
            13 => {
                if v_isShared_6394_ == 0 {
                    v___x_6396_ = v___x_6393_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6397_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6397_, 0, v_a_6391_);
                    v___x_6396_ = v_reuseFailAlloc_6397_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6396_;
            }
            15 => {
                v___x_6405_ = 0u64;
                v___x_6406_ = leanh::lean_box(0);
                v___x_6407_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8;
                v___x_6408_ = leanh::lean_box(0);
                v___x_6409_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0;
                v___x_6410_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_6410_, 0, v___x_6407_);
                leanh::lean_ctor_set(v___x_6410_, 1, v___x_6408_);
                leanh::lean_ctor_set(v___x_6410_, 2, v___x_6409_);
                leanh::lean_ctor_set_float(
                    v___x_6410_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_6401_,
                );
                leanh::lean_ctor_set_float(
                    v___x_6410_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_6403_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6410_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_6275_,
                );
                v___x_6411_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
                v___x_6412_ = lean_mk_empty_array_with_capacity(v___x_6242_);
                v___x_6413_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6413_, 0, v___x_6410_);
                leanh::lean_ctor_set(v___x_6413_, 1, v___x_6411_);
                leanh::lean_ctor_set(v___x_6413_, 2, v___x_6412_);
                v___x_6414_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6414_, 0, v___x_6406_);
                leanh::lean_ctor_set(v___x_6414_, 1, v___x_6413_);
                v___x_6415_ = leanh::lean_unsigned_to_nat(1);
                v___x_6416_ = lean_mk_empty_array_with_capacity(v___x_6415_);
                v___x_6417_ = lean_array_push(v___x_6416_, v___x_6414_);
                v___x_6418_ = l_Array_toPArray_x27___redArg(v___x_6417_);
                leanh::lean_dec_ref(v___x_6417_);
                v___x_6419_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_6419_, 0, v___x_6418_);
                leanh::lean_ctor_set_uint64(
                    v___x_6419_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_6405_,
                );
                v_traceState_6307_ = v___x_6419_;
                state = 9;
                continue;
            }
            16 => {
                return v___x_6449_;
            }
            17 => {
                if v_isShared_6456_ == 0 {
                    v___x_6458_ = v___x_6455_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6459_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6459_, 0, v_a_6453_);
                    v___x_6458_ = v_reuseFailAlloc_6459_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6458_;
            }
            19 => {
                if v_isShared_6467_ == 0 {
                    v___x_6469_ = v___x_6466_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6470_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6470_, 0, v_a_6464_);
                    v___x_6469_ = v_reuseFailAlloc_6470_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(
    mut v_setupImports_6472_: *mut leanh::LeanObject,
    mut v_stx_6473_: *mut leanh::LeanObject,
    mut v_origStx_6474_: *mut leanh::LeanObject,
    mut v_toProcessingContext_6475_: *mut leanh::LeanObject,
    mut v___x_6476_: *mut leanh::LeanObject,
    mut v_fileMap_6477_: *mut leanh::LeanObject,
    mut v_parserState_6478_: *mut leanh::LeanObject,
    mut v_a_6479_: *mut leanh::LeanObject,
    mut v___x_6480_: *mut leanh::LeanObject,
    mut v___x_6481_: *mut leanh::LeanObject,
    mut v___y_6482_: *mut leanh::LeanObject,
    mut v___y_6483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6484_ =
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(
            v_setupImports_6472_,
            v_stx_6473_,
            v_origStx_6474_,
            v_toProcessingContext_6475_,
            v___x_6476_,
            v_fileMap_6477_,
            v_parserState_6478_,
            v_a_6479_,
            v___x_6480_,
            v___x_6481_,
            v___y_6482_,
        );
    leanh::lean_dec_ref(v___y_6482_);
    leanh::lean_dec_ref(v_a_6479_);
    return v_res_6484_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6485_ = l_Lean_Language_instInhabitedSnapshotLeaf;
    v___f_6486_ = leanh::lean_alloc_closure(
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_6486_, 0, v___x_6485_);
    return v___f_6486_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(
    mut v_setupImports_6487_: *mut leanh::LeanObject,
    mut v_stx_6488_: *mut leanh::LeanObject,
    mut v_origStx_6489_: *mut leanh::LeanObject,
    mut v_parserState_6490_: *mut leanh::LeanObject,
    mut v_a_6491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toProcessingContext_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toProcessingContext_6493_ = leanh::lean_ctor_get(v_a_6491_, 0);
    v_fileMap_6494_ = leanh::lean_ctor_get(v_toProcessingContext_6493_, 2);
    v_endPos_6495_ = leanh::lean_ctor_get(v_toProcessingContext_6493_, 3);
    v___x_6496_ = l_Lean_Language_instInhabitedSnapshotLeaf;
    v___f_6497_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
    v___x_6498_ = leanh::lean_box(0);
    v___x_6499_ = leanh::lean_unsigned_to_nat(0);
    leanh::lean_inc_ref_n(v_a_6491_, 2);
    leanh::lean_inc_ref(v_fileMap_6494_);
    leanh::lean_inc_ref(v_toProcessingContext_6493_);
    v___f_6500_ = leanh::lean_alloc_closure(
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed
            as *mut core::ffi::c_void,
        12,
        10,
    );
    leanh::lean_closure_set(v___f_6500_, 0, v_setupImports_6487_);
    leanh::lean_closure_set(v___f_6500_, 1, v_stx_6488_);
    leanh::lean_closure_set(v___f_6500_, 2, v_origStx_6489_);
    leanh::lean_closure_set(v___f_6500_, 3, v_toProcessingContext_6493_);
    leanh::lean_closure_set(v___f_6500_, 4, v___x_6499_);
    leanh::lean_closure_set(v___f_6500_, 5, v_fileMap_6494_);
    leanh::lean_closure_set(v___f_6500_, 6, v_parserState_6490_);
    leanh::lean_closure_set(v___f_6500_, 7, v_a_6491_);
    leanh::lean_closure_set(v___f_6500_, 8, v___x_6498_);
    leanh::lean_closure_set(v___f_6500_, 9, v___x_6496_);
    leanh::lean_inc(v_endPos_6495_);
    v___x_6501_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6501_, 0, v___x_6499_);
    leanh::lean_ctor_set(v___x_6501_, 1, v_endPos_6495_);
    v___x_6502_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6502_, 0, v___x_6501_);
    v___x_6503_ = leanh::lean_alloc_closure(
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_6503_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6503_, 1, v___f_6497_);
    leanh::lean_closure_set(v___x_6503_, 2, v___f_6500_);
    leanh::lean_closure_set(v___x_6503_, 3, v_a_6491_);
    v___x_6504_ = l_Lean_Language_SnapshotTask_ofIO___redArg(
        v___x_6498_,
        v___x_6498_,
        v___x_6502_,
        v___x_6503_,
    );
    return v___x_6504_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(
    mut v_setupImports_6505_: *mut leanh::LeanObject,
    mut v_stx_6506_: *mut leanh::LeanObject,
    mut v_origStx_6507_: *mut leanh::LeanObject,
    mut v_parserState_6508_: *mut leanh::LeanObject,
    mut v_a_6509_: *mut leanh::LeanObject,
    mut v_a_6510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6511_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(
        v_setupImports_6505_,
        v_stx_6506_,
        v_origStx_6507_,
        v_parserState_6508_,
        v_a_6509_,
    );
    leanh::lean_dec_ref(v_a_6509_);
    return v_res_6511_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6512_ = leanh::lean_box(0);
    v___x_6513_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_6512_);
    return v___x_6513_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6518_: u8 = 0;
    let mut v___x_6519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6518_ = 1;
    v___x_6519_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2;
    v___x_6520_ = l_Lean_Name_toString(v___x_6519_, v___x_6518_);
    return v___x_6520_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_6521_: u8 = 0;
    let mut v___x_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6521_ = 0;
    v___x_6522_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
    v___x_6523_ = leanh::lean_box(0);
    v___x_6524_ = l_Lean_Language_Snapshot_Diagnostics_empty;
    v___x_6525_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
    v___x_6526_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
    leanh::lean_ctor_set(v___x_6526_, 0, v___x_6525_);
    leanh::lean_ctor_set(v___x_6526_, 1, v___x_6524_);
    leanh::lean_ctor_set(v___x_6526_, 2, v___x_6523_);
    leanh::lean_ctor_set(v___x_6526_, 3, v___x_6522_);
    leanh::lean_ctor_set_uint8(
        v___x_6526_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        v___x_6521_,
    );
    return v___x_6526_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(
    mut v_newParserState_6527_: *mut leanh::LeanObject,
    mut v_cmdState_6528_: *mut leanh::LeanObject,
    mut v_a_6529_: *mut leanh::LeanObject,
    mut v_toSnapshot_6530_: *mut leanh::LeanObject,
    mut v_newStx_6531_: *mut leanh::LeanObject,
    mut v_oldCmd_6532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: u8 = 0;
    let mut v___x_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6542_: u8 = 0;
    let mut v___x_6543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: u8 = 0;
    let mut v___x_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6561_: u8 = 0;
    let mut v_unused_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6534_ = lean_io_promise_new();
                v___x_6535_ = l_IO_CancelToken_new();
                v___x_6536_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6536_, 0, v_oldCmd_6532_);
                v___x_6537_ = 1;
                leanh::lean_inc_ref(v___x_6535_);
                leanh::lean_inc(v___x_6534_);
                leanh::lean_inc_ref(v_cmdState_6528_);
                v___x_6538_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(
                    v___x_6536_,
                    v_newParserState_6527_,
                    v_cmdState_6528_,
                    v___x_6534_,
                    v___x_6537_,
                    v___x_6535_,
                    v_a_6529_,
                );
                v_diagnostics_6539_ = leanh::lean_ctor_get(v_toSnapshot_6530_, 1);
                v_isSharedCheck_6561_ =
                    (!leanh::lean_is_exclusive(v_toSnapshot_6530_)) as u8;
                if v_isSharedCheck_6561_ == 0 {
                    v_unused_6562_ = leanh::lean_ctor_get(v_toSnapshot_6530_, 3);
                    leanh::lean_dec(v_unused_6562_);
                    v_unused_6563_ = leanh::lean_ctor_get(v_toSnapshot_6530_, 2);
                    leanh::lean_dec(v_unused_6563_);
                    v_unused_6564_ = leanh::lean_ctor_get(v_toSnapshot_6530_, 0);
                    leanh::lean_dec(v_unused_6564_);
                    v___x_6541_ = v_toSnapshot_6530_;
                    v_isShared_6542_ = v_isSharedCheck_6561_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diagnostics_6539_);
                    leanh::lean_dec(v_toSnapshot_6530_);
                    v___x_6541_ = leanh::lean_box(0);
                    v_isShared_6542_ = v_isSharedCheck_6561_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6543_ = leanh::lean_box(0);
                v___x_6544_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
                v___x_6545_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
                v___x_6546_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
                v___x_6547_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6547_, 0, v___x_6535_);
                v___x_6548_ = l_IO_Promise_result_x21___redArg(v___x_6534_);
                leanh::lean_dec(v___x_6534_);
                v___x_6549_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_6549_, 0, v___x_6543_);
                leanh::lean_ctor_set(v___x_6549_, 1, v___x_6544_);
                leanh::lean_ctor_set(v___x_6549_, 2, v___x_6547_);
                leanh::lean_ctor_set(v___x_6549_, 3, v___x_6548_);
                v___x_6550_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6550_, 0, v_cmdState_6528_);
                leanh::lean_ctor_set(v___x_6550_, 1, v___x_6549_);
                v___x_6551_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6551_, 0, v___x_6550_);
                v___x_6552_ = 0;
                v___x_6553_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
                v___x_6554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6554_, 0, v_newStx_6531_);
                if v_isShared_6542_ == 0 {
                    leanh::lean_ctor_set(v___x_6541_, 3, v___x_6546_);
                    leanh::lean_ctor_set(v___x_6541_, 2, v___x_6543_);
                    leanh::lean_ctor_set(v___x_6541_, 0, v___x_6545_);
                    v___x_6556_ = v___x_6541_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6560_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6560_, 0, v___x_6545_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6560_, 1, v_diagnostics_6539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6560_, 2, v___x_6543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6560_, 3, v___x_6546_);
                    v___x_6556_ = v_reuseFailAlloc_6560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_6556_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_6552_,
                );
                v___x_6557_ =
                    l_Lean_Language_SnapshotTask_finished___redArg(v___x_6554_, v___x_6556_);
                v___x_6558_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6558_, 0, v___x_6553_);
                leanh::lean_ctor_set(v___x_6558_, 1, v___x_6557_);
                leanh::lean_ctor_set(v___x_6558_, 2, v___x_6551_);
                v___x_6559_ =
                    l_Lean_Language_SnapshotTask_finished___redArg(v___x_6543_, v___x_6558_);
                return v___x_6559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(
    mut v_newParserState_6565_: *mut leanh::LeanObject,
    mut v_cmdState_6566_: *mut leanh::LeanObject,
    mut v_a_6567_: *mut leanh::LeanObject,
    mut v_toSnapshot_6568_: *mut leanh::LeanObject,
    mut v_newStx_6569_: *mut leanh::LeanObject,
    mut v_oldCmd_6570_: *mut leanh::LeanObject,
    mut v___y_6571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6572_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(
        v_newParserState_6565_,
        v_cmdState_6566_,
        v_a_6567_,
        v_toSnapshot_6568_,
        v_newStx_6569_,
        v_oldCmd_6570_,
    );
    leanh::lean_dec_ref(v_a_6567_);
    return v_res_6572_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(
    mut v_newParserState_6573_: *mut leanh::LeanObject,
    mut v_a_6574_: *mut leanh::LeanObject,
    mut v_newStx_6575_: *mut leanh::LeanObject,
    mut v___x_6576_: *mut leanh::LeanObject,
    mut v_oldProcessed_6577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_result_x3f_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_result_x3f_6579_ = leanh::lean_ctor_get(v_oldProcessed_6577_, 2);
    if leanh::lean_obj_tag(v_result_x3f_6579_) == 1 {
        let mut v_val_6580_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_firstCmdSnap_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toSnapshot_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_cmdState_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_stx_x3f_6584_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6585_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6587_: u8 = 0;
        let mut v___x_6588_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6580_ = leanh::lean_ctor_get(v_result_x3f_6579_, 0);
        leanh::lean_inc(v_val_6580_);
        v_firstCmdSnap_6581_ = leanh::lean_ctor_get(v_val_6580_, 1);
        leanh::lean_inc_ref(v_firstCmdSnap_6581_);
        v_toSnapshot_6582_ = leanh::lean_ctor_get(v_oldProcessed_6577_, 0);
        leanh::lean_inc_ref(v_toSnapshot_6582_);
        leanh::lean_dec_ref(v_oldProcessed_6577_);
        v_cmdState_6583_ = leanh::lean_ctor_get(v_val_6580_, 0);
        leanh::lean_inc_ref(v_cmdState_6583_);
        leanh::lean_dec(v_val_6580_);
        v_stx_x3f_6584_ = leanh::lean_ctor_get(v_firstCmdSnap_6581_, 0);
        leanh::lean_inc(v_stx_x3f_6584_);
        leanh::lean_inc_ref(v_a_6574_);
        v___f_6585_ = leanh::lean_alloc_closure(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed as *mut core::ffi::c_void, 7, 5);
        leanh::lean_closure_set(v___f_6585_, 0, v_newParserState_6573_);
        leanh::lean_closure_set(v___f_6585_, 1, v_cmdState_6583_);
        leanh::lean_closure_set(v___f_6585_, 2, v_a_6574_);
        leanh::lean_closure_set(v___f_6585_, 3, v_toSnapshot_6582_);
        leanh::lean_closure_set(v___f_6585_, 4, v_newStx_6575_);
        v___x_6586_ = leanh::lean_box(0);
        v___x_6587_ = 1;
        v___x_6588_ = l_Lean_Language_SnapshotTask_bindIO___redArg(
            v_firstCmdSnap_6581_,
            v___f_6585_,
            v_stx_x3f_6584_,
            v___x_6576_,
            v___x_6586_,
            v___x_6587_,
        );
        return v___x_6588_;
    } else {
        let mut v___x_6589_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_6576_);
        leanh::lean_dec_ref(v_newParserState_6573_);
        v___x_6589_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6589_, 0, v_newStx_6575_);
        v___x_6590_ =
            l_Lean_Language_SnapshotTask_finished___redArg(v___x_6589_, v_oldProcessed_6577_);
        return v___x_6590_;
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(
    mut v_newParserState_6591_: *mut leanh::LeanObject,
    mut v_a_6592_: *mut leanh::LeanObject,
    mut v_newStx_6593_: *mut leanh::LeanObject,
    mut v___x_6594_: *mut leanh::LeanObject,
    mut v_oldProcessed_6595_: *mut leanh::LeanObject,
    mut v___y_6596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6597_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(
        v_newParserState_6591_,
        v_a_6592_,
        v_newStx_6593_,
        v___x_6594_,
        v_oldProcessed_6595_,
    );
    leanh::lean_dec_ref(v_a_6592_);
    return v_res_6597_;
}
pub unsafe fn _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6598_: u8 = 0;
    let mut v___x_6599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6598_ = 0;
    v___x_6599_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
    v___x_6600_ = leanh::lean_box(0);
    v___x_6601_ = l_Lean_Language_Snapshot_Diagnostics_empty;
    v___x_6602_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
    v___x_6603_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
    leanh::lean_ctor_set(v___x_6603_, 0, v___x_6602_);
    leanh::lean_ctor_set(v___x_6603_, 1, v___x_6601_);
    leanh::lean_ctor_set(v___x_6603_, 2, v___x_6600_);
    leanh::lean_ctor_set(v___x_6603_, 3, v___x_6599_);
    leanh::lean_ctor_set_uint8(
        v___x_6603_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        v___x_6598_,
    );
    return v___x_6603_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(
    mut v_toProcessingContext_6604_: *mut leanh::LeanObject,
    mut v_a_6605_: *mut leanh::LeanObject,
    mut v_old_6606_: *mut leanh::LeanObject,
    mut v_newStx_6607_: *mut leanh::LeanObject,
    mut v_newParserState_6608_: *mut leanh::LeanObject,
    mut v___y_6609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_result_x3f_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6615_: u8 = 0;
    let mut v_processedSnap_6616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6619_: u8 = 0;
    let mut v_toSnapshot_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6623_: u8 = 0;
    let mut v_pos_6624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_6625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: u8 = 0;
    let mut v___x_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_6633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6636_: u8 = 0;
    let mut v___x_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: u8 = 0;
    let mut v___x_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6655_: u8 = 0;
    let mut v_unused_6656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6659_: u8 = 0;
    let mut v_unused_6660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6664_: u8 = 0;
    let mut v_unused_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6666_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_result_x3f_6611_ = leanh::lean_ctor_get(v_old_6606_, 4);
                leanh::lean_inc(v_result_x3f_6611_);
                if leanh::lean_obj_tag(v_result_x3f_6611_) == 1 {
                    v_val_6612_ = leanh::lean_ctor_get(v_result_x3f_6611_, 0);
                    v_isSharedCheck_6666_ =
                        (!leanh::lean_is_exclusive(v_result_x3f_6611_)) as u8;
                    if v_isSharedCheck_6666_ == 0 {
                        v___x_6614_ = v_result_x3f_6611_;
                        v_isShared_6615_ = v_isSharedCheck_6666_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6612_);
                        leanh::lean_dec(v_result_x3f_6611_);
                        v___x_6614_ = leanh::lean_box(0);
                        v_isShared_6615_ = v_isSharedCheck_6666_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_result_x3f_6611_);
                    leanh::lean_dec_ref(v_newParserState_6608_);
                    leanh::lean_dec(v_newStx_6607_);
                    leanh::lean_dec_ref(v_toProcessingContext_6604_);
                    return v_old_6606_;
                }
            }
            1 => {
                v_processedSnap_6616_ = leanh::lean_ctor_get(v_val_6612_, 1);
                v_isSharedCheck_6664_ = (!leanh::lean_is_exclusive(v_val_6612_)) as u8;
                if v_isSharedCheck_6664_ == 0 {
                    v_unused_6665_ = leanh::lean_ctor_get(v_val_6612_, 0);
                    leanh::lean_dec(v_unused_6665_);
                    v___x_6618_ = v_val_6612_;
                    v_isShared_6619_ = v_isSharedCheck_6664_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_processedSnap_6616_);
                    leanh::lean_dec(v_val_6612_);
                    v___x_6618_ = leanh::lean_box(0);
                    v_isShared_6619_ = v_isSharedCheck_6664_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_toSnapshot_6620_ = leanh::lean_ctor_get(v_old_6606_, 0);
                v_isSharedCheck_6659_ = (!leanh::lean_is_exclusive(v_old_6606_)) as u8;
                if v_isSharedCheck_6659_ == 0 {
                    v_unused_6660_ = leanh::lean_ctor_get(v_old_6606_, 4);
                    leanh::lean_dec(v_unused_6660_);
                    v_unused_6661_ = leanh::lean_ctor_get(v_old_6606_, 3);
                    leanh::lean_dec(v_unused_6661_);
                    v_unused_6662_ = leanh::lean_ctor_get(v_old_6606_, 2);
                    leanh::lean_dec(v_unused_6662_);
                    v_unused_6663_ = leanh::lean_ctor_get(v_old_6606_, 1);
                    leanh::lean_dec(v_unused_6663_);
                    v___x_6622_ = v_old_6606_;
                    v_isShared_6623_ = v_isSharedCheck_6659_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_toSnapshot_6620_);
                    leanh::lean_dec(v_old_6606_);
                    v___x_6622_ = leanh::lean_box(0);
                    v_isShared_6623_ = v_isSharedCheck_6659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_pos_6624_ = leanh::lean_ctor_get(v_newParserState_6608_, 0);
                v_endPos_6625_ = leanh::lean_ctor_get(v_toProcessingContext_6604_, 3);
                v_stx_x3f_6626_ = leanh::lean_ctor_get(v_processedSnap_6616_, 0);
                leanh::lean_inc(v_stx_x3f_6626_);
                leanh::lean_inc(v_endPos_6625_);
                leanh::lean_inc(v_pos_6624_);
                v___x_6627_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6627_, 0, v_pos_6624_);
                leanh::lean_ctor_set(v___x_6627_, 1, v_endPos_6625_);
                v___x_6628_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6628_, 0, v___x_6627_);
                leanh::lean_inc_ref(v___x_6628_);
                leanh::lean_inc(v_newStx_6607_);
                leanh::lean_inc_ref(v_a_6605_);
                leanh::lean_inc_ref(v_newParserState_6608_);
                v___f_6629_ = leanh::lean_alloc_closure(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed as *mut core::ffi::c_void, 6, 4);
                leanh::lean_closure_set(v___f_6629_, 0, v_newParserState_6608_);
                leanh::lean_closure_set(v___f_6629_, 1, v_a_6605_);
                leanh::lean_closure_set(v___f_6629_, 2, v_newStx_6607_);
                leanh::lean_closure_set(v___f_6629_, 3, v___x_6628_);
                v___x_6630_ = leanh::lean_box(0);
                v___x_6631_ = 1;
                v___x_6632_ = l_Lean_Language_SnapshotTask_bindIO___redArg(
                    v_processedSnap_6616_,
                    v___f_6629_,
                    v_stx_x3f_6626_,
                    v___x_6628_,
                    v___x_6630_,
                    v___x_6631_,
                );
                v_diagnostics_6633_ = leanh::lean_ctor_get(v_toSnapshot_6620_, 1);
                v_isSharedCheck_6655_ =
                    (!leanh::lean_is_exclusive(v_toSnapshot_6620_)) as u8;
                if v_isSharedCheck_6655_ == 0 {
                    v_unused_6656_ = leanh::lean_ctor_get(v_toSnapshot_6620_, 3);
                    leanh::lean_dec(v_unused_6656_);
                    v_unused_6657_ = leanh::lean_ctor_get(v_toSnapshot_6620_, 2);
                    leanh::lean_dec(v_unused_6657_);
                    v_unused_6658_ = leanh::lean_ctor_get(v_toSnapshot_6620_, 0);
                    leanh::lean_dec(v_unused_6658_);
                    v___x_6635_ = v_toSnapshot_6620_;
                    v_isShared_6636_ = v_isSharedCheck_6655_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_diagnostics_6633_);
                    leanh::lean_dec(v_toSnapshot_6620_);
                    v___x_6635_ = leanh::lean_box(0);
                    v_isShared_6636_ = v_isSharedCheck_6655_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6637_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
                v___x_6638_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
                if v_isShared_6619_ == 0 {
                    leanh::lean_ctor_set(v___x_6618_, 1, v___x_6632_);
                    leanh::lean_ctor_set(v___x_6618_, 0, v_newParserState_6608_);
                    v___x_6640_ = v___x_6618_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6654_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6654_, 0, v_newParserState_6608_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6654_, 1, v___x_6632_);
                    v___x_6640_ = v_reuseFailAlloc_6654_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6615_ == 0 {
                    leanh::lean_ctor_set(v___x_6614_, 0, v___x_6640_);
                    v___x_6642_ = v___x_6614_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6653_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6653_, 0, v___x_6640_);
                    v___x_6642_ = v_reuseFailAlloc_6653_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6643_ = 0;
                v___x_6644_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
                leanh::lean_inc(v_newStx_6607_);
                v___x_6645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6645_, 0, v_newStx_6607_);
                if v_isShared_6636_ == 0 {
                    leanh::lean_ctor_set(v___x_6635_, 3, v___x_6638_);
                    leanh::lean_ctor_set(v___x_6635_, 2, v___x_6630_);
                    leanh::lean_ctor_set(v___x_6635_, 0, v___x_6637_);
                    v___x_6647_ = v___x_6635_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6652_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 0, v___x_6637_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 1, v_diagnostics_6633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 2, v___x_6630_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6652_, 3, v___x_6638_);
                    v___x_6647_ = v_reuseFailAlloc_6652_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_ctor_set_uint8(
                    v___x_6647_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_6643_,
                );
                v___x_6648_ =
                    l_Lean_Language_SnapshotTask_finished___redArg(v___x_6645_, v___x_6647_);
                if v_isShared_6623_ == 0 {
                    leanh::lean_ctor_set(v___x_6622_, 4, v___x_6642_);
                    leanh::lean_ctor_set(v___x_6622_, 3, v_newStx_6607_);
                    leanh::lean_ctor_set(v___x_6622_, 2, v_toProcessingContext_6604_);
                    leanh::lean_ctor_set(v___x_6622_, 1, v___x_6648_);
                    leanh::lean_ctor_set(v___x_6622_, 0, v___x_6644_);
                    v___x_6650_ = v___x_6622_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6651_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6651_, 0, v___x_6644_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6651_, 1, v___x_6648_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6651_,
                        2,
                        v_toProcessingContext_6604_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6651_, 3, v_newStx_6607_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6651_, 4, v___x_6642_);
                    v___x_6650_ = v_reuseFailAlloc_6651_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(
    mut v_toProcessingContext_6667_: *mut leanh::LeanObject,
    mut v_a_6668_: *mut leanh::LeanObject,
    mut v_old_6669_: *mut leanh::LeanObject,
    mut v_newStx_6670_: *mut leanh::LeanObject,
    mut v_newParserState_6671_: *mut leanh::LeanObject,
    mut v___y_6672_: *mut leanh::LeanObject,
    mut v___y_6673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6674_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(
        v_toProcessingContext_6667_,
        v_a_6668_,
        v_old_6669_,
        v_newStx_6670_,
        v_newParserState_6671_,
        v___y_6672_,
    );
    leanh::lean_dec_ref(v___y_6672_);
    leanh::lean_dec_ref(v_a_6668_);
    return v_res_6674_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(
    mut v_toProcessingContext_6675_: *mut leanh::LeanObject,
    mut v_setupImports_6676_: *mut leanh::LeanObject,
    mut v_old_x3f_6677_: *mut leanh::LeanObject,
    mut v___f_6678_: *mut leanh::LeanObject,
    mut v___y_6679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6685_: u8 = 0;
    let mut v_snd_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6692_: u8 = 0;
    let mut v___x_6693_: u8 = 0;
    let mut v___x_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6720_: u8 = 0;
    let mut v_stx_6721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_x3f_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: u8 = 0;
    let mut v_val_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_processedSnap_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6733_: u8 = 0;
    let mut v___x_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: u8 = 0;
    let mut v___x_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6750_: u8 = 0;
    let mut v_isSharedCheck_6751_: u8 = 0;
    let mut v_a_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6755_: u8 = 0;
    let mut v___x_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_toProcessingContext_6675_);
                v___x_6681_ = l_Lean_Parser_parseHeader(v_toProcessingContext_6675_);
                if leanh::lean_obj_tag(v___x_6681_) == 0 {
                    v_a_6682_ = leanh::lean_ctor_get(v___x_6681_, 0);
                    v_isSharedCheck_6751_ = (!leanh::lean_is_exclusive(v___x_6681_)) as u8;
                    if v_isSharedCheck_6751_ == 0 {
                        v___x_6684_ = v___x_6681_;
                        v_isShared_6685_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6682_);
                        leanh::lean_dec(v___x_6681_);
                        v___x_6684_ = leanh::lean_box(0);
                        v_isShared_6685_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_6678_);
                    leanh::lean_dec(v_old_x3f_6677_);
                    leanh::lean_dec_ref(v_setupImports_6676_);
                    leanh::lean_dec_ref(v_toProcessingContext_6675_);
                    v_a_6752_ = leanh::lean_ctor_get(v___x_6681_, 0);
                    v_isSharedCheck_6759_ = (!leanh::lean_is_exclusive(v___x_6681_)) as u8;
                    if v_isSharedCheck_6759_ == 0 {
                        v___x_6754_ = v___x_6681_;
                        v_isShared_6755_ = v_isSharedCheck_6759_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6752_);
                        leanh::lean_dec(v___x_6681_);
                        v___x_6754_ = leanh::lean_box(0);
                        v_isShared_6755_ = v_isSharedCheck_6759_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_6686_ = leanh::lean_ctor_get(v_a_6682_, 1);
                leanh::lean_inc(v_snd_6686_);
                v_fst_6687_ = leanh::lean_ctor_get(v_a_6682_, 0);
                leanh::lean_inc(v_fst_6687_);
                leanh::lean_dec(v_a_6682_);
                v_fst_6688_ = leanh::lean_ctor_get(v_snd_6686_, 0);
                v_snd_6689_ = leanh::lean_ctor_get(v_snd_6686_, 1);
                v_isSharedCheck_6750_ = (!leanh::lean_is_exclusive(v_snd_6686_)) as u8;
                if v_isSharedCheck_6750_ == 0 {
                    v___x_6691_ = v_snd_6686_;
                    v_isShared_6692_ = v_isSharedCheck_6750_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6689_);
                    leanh::lean_inc(v_fst_6688_);
                    leanh::lean_dec(v_snd_6686_);
                    v___x_6691_ = leanh::lean_box(0);
                    v_isShared_6692_ = v_isSharedCheck_6750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6693_ = l_Lean_MessageLog_hasErrors(v_snd_6689_);
                if v___x_6693_ == 0 {
                    leanh::lean_inc(v_fst_6687_);
                    v___x_6694_ = l_Lean_Syntax_unsetTrailing(v_fst_6687_);
                    if leanh::lean_obj_tag(v_old_x3f_6677_) == 1 {
                        v_val_6717_ = leanh::lean_ctor_get(v_old_x3f_6677_, 0);
                        v_isSharedCheck_6733_ =
                            (!leanh::lean_is_exclusive(v_old_x3f_6677_)) as u8;
                        if v_isSharedCheck_6733_ == 0 {
                            v___x_6719_ = v_old_x3f_6677_;
                            v_isShared_6720_ = v_isSharedCheck_6733_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_6717_);
                            leanh::lean_dec(v_old_x3f_6677_);
                            v___x_6719_ = leanh::lean_box(0);
                            v_isShared_6720_ = v_isSharedCheck_6733_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___f_6678_);
                        leanh::lean_dec(v_old_x3f_6677_);
                        v___y_6696_ = v___y_6679_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6691_);
                    leanh::lean_dec(v_fst_6688_);
                    leanh::lean_dec_ref(v___f_6678_);
                    leanh::lean_dec(v_old_x3f_6677_);
                    leanh::lean_dec_ref(v_setupImports_6676_);
                    v___x_6734_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_6689_);
                    v___x_6735_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
                    v___x_6736_ = l_Lean_Language_Snapshot_Diagnostics_empty;
                    v___x_6737_ = leanh::lean_box(0);
                    v___x_6738_ = leanh::lean_unsigned_to_nat(32);
                    v___x_6739_ = lean_mk_empty_array_with_capacity(v___x_6738_);
                    leanh::lean_dec_ref(v___x_6739_);
                    v___x_6740_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
                    v___x_6741_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v___x_6741_, 0, v___x_6735_);
                    leanh::lean_ctor_set(v___x_6741_, 1, v___x_6736_);
                    leanh::lean_ctor_set(v___x_6741_, 2, v___x_6737_);
                    leanh::lean_ctor_set(v___x_6741_, 3, v___x_6740_);
                    leanh::lean_ctor_set_uint8(
                        v___x_6741_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v___x_6693_,
                    );
                    leanh::lean_inc(v_fst_6687_);
                    v___x_6742_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6742_, 0, v_fst_6687_);
                    v___x_6743_ = 0;
                    v___x_6744_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v___x_6744_, 0, v___x_6735_);
                    leanh::lean_ctor_set(v___x_6744_, 1, v___x_6734_);
                    leanh::lean_ctor_set(v___x_6744_, 2, v___x_6737_);
                    leanh::lean_ctor_set(v___x_6744_, 3, v___x_6740_);
                    leanh::lean_ctor_set_uint8(
                        v___x_6744_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v___x_6743_,
                    );
                    v___x_6745_ =
                        l_Lean_Language_SnapshotTask_finished___redArg(v___x_6742_, v___x_6744_);
                    v___x_6746_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_6746_, 0, v___x_6741_);
                    leanh::lean_ctor_set(v___x_6746_, 1, v___x_6745_);
                    leanh::lean_ctor_set(v___x_6746_, 2, v_toProcessingContext_6675_);
                    leanh::lean_ctor_set(v___x_6746_, 3, v_fst_6687_);
                    leanh::lean_ctor_set(v___x_6746_, 4, v___x_6737_);
                    if v_isShared_6685_ == 0 {
                        leanh::lean_ctor_set(v___x_6684_, 0, v___x_6746_);
                        v___x_6748_ = v___x_6684_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6749_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6749_, 0, v___x_6746_);
                        v___x_6748_ = v_reuseFailAlloc_6749_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6697_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_6689_);
                leanh::lean_inc(v_fst_6688_);
                leanh::lean_inc(v_fst_6687_);
                v___x_6698_ =
                    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(
                        v_setupImports_6676_,
                        v___x_6694_,
                        v_fst_6687_,
                        v_fst_6688_,
                        v___y_6696_,
                    );
                v___x_6699_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
                v___x_6700_ = l_Lean_Language_Snapshot_Diagnostics_empty;
                v___x_6701_ = leanh::lean_box(0);
                v___x_6702_ = leanh::lean_unsigned_to_nat(32);
                v___x_6703_ = lean_mk_empty_array_with_capacity(v___x_6702_);
                leanh::lean_dec_ref(v___x_6703_);
                v___x_6704_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once), _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
                if v_isShared_6692_ == 0 {
                    leanh::lean_ctor_set(v___x_6691_, 1, v___x_6698_);
                    v___x_6706_ = v___x_6691_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6716_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 0, v_fst_6688_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 1, v___x_6698_);
                    v___x_6706_ = v_reuseFailAlloc_6716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6707_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6707_, 0, v___x_6706_);
                v___x_6708_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_6708_, 0, v___x_6699_);
                leanh::lean_ctor_set(v___x_6708_, 1, v___x_6700_);
                leanh::lean_ctor_set(v___x_6708_, 2, v___x_6701_);
                leanh::lean_ctor_set(v___x_6708_, 3, v___x_6704_);
                leanh::lean_ctor_set_uint8(
                    v___x_6708_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_6693_,
                );
                leanh::lean_inc(v_fst_6687_);
                v___x_6709_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6709_, 0, v_fst_6687_);
                v___x_6710_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_6710_, 0, v___x_6699_);
                leanh::lean_ctor_set(v___x_6710_, 1, v___x_6697_);
                leanh::lean_ctor_set(v___x_6710_, 2, v___x_6701_);
                leanh::lean_ctor_set(v___x_6710_, 3, v___x_6704_);
                leanh::lean_ctor_set_uint8(
                    v___x_6710_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_6693_,
                );
                v___x_6711_ =
                    l_Lean_Language_SnapshotTask_finished___redArg(v___x_6709_, v___x_6710_);
                v___x_6712_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_6712_, 0, v___x_6708_);
                leanh::lean_ctor_set(v___x_6712_, 1, v___x_6711_);
                leanh::lean_ctor_set(v___x_6712_, 2, v_toProcessingContext_6675_);
                leanh::lean_ctor_set(v___x_6712_, 3, v_fst_6687_);
                leanh::lean_ctor_set(v___x_6712_, 4, v___x_6707_);
                if v_isShared_6685_ == 0 {
                    leanh::lean_ctor_set(v___x_6684_, 0, v___x_6712_);
                    v___x_6714_ = v___x_6684_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6715_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6715_, 0, v___x_6712_);
                    v___x_6714_ = v_reuseFailAlloc_6715_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6714_;
            }
            6 => {
                v_stx_6721_ = leanh::lean_ctor_get(v_val_6717_, 3);
                v_result_x3f_6722_ = leanh::lean_ctor_get(v_val_6717_, 4);
                leanh::lean_inc(v_stx_6721_);
                v___x_6723_ = l_Lean_Syntax_unsetTrailing(v_stx_6721_);
                leanh::lean_inc(v___x_6694_);
                v___x_6724_ = l_Lean_Syntax_eqWithInfo(v___x_6694_, v___x_6723_);
                if v___x_6724_ == 0 {
                    leanh::lean_inc(v_result_x3f_6722_);
                    leanh::lean_del_object(v___x_6719_);
                    leanh::lean_dec(v_val_6717_);
                    leanh::lean_dec_ref(v___f_6678_);
                    if leanh::lean_obj_tag(v_result_x3f_6722_) == 0 {
                        v___y_6696_ = v___y_6679_;
                        state = 3;
                        continue;
                    } else {
                        v_val_6725_ = leanh::lean_ctor_get(v_result_x3f_6722_, 0);
                        leanh::lean_inc(v_val_6725_);
                        leanh::lean_dec_ref_known(v_result_x3f_6722_, 1);
                        v_processedSnap_6726_ = leanh::lean_ctor_get(v_val_6725_, 1);
                        leanh::lean_inc_ref(v_processedSnap_6726_);
                        leanh::lean_dec(v_val_6725_);
                        v___x_6727_ =
                            l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
                        v___x_6728_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(
                            v___x_6727_,
                            v_processedSnap_6726_,
                        );
                        v___y_6696_ = v___y_6679_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_6694_);
                    leanh::lean_del_object(v___x_6691_);
                    leanh::lean_dec(v_snd_6689_);
                    leanh::lean_del_object(v___x_6684_);
                    leanh::lean_dec_ref(v_setupImports_6676_);
                    leanh::lean_dec_ref(v_toProcessingContext_6675_);
                    leanh::lean_inc_ref(v___y_6679_);
                    v___x_6729_ = leanh::lean_apply_5(
                        v___f_6678_,
                        v_val_6717_,
                        v_fst_6687_,
                        v_fst_6688_,
                        v___y_6679_,
                        leanh::lean_box(0),
                    );
                    if v_isShared_6720_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6719_, 0);
                        leanh::lean_ctor_set(v___x_6719_, 0, v___x_6729_);
                        v___x_6731_ = v___x_6719_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6732_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6732_, 0, v___x_6729_);
                        v___x_6731_ = v_reuseFailAlloc_6732_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_6731_;
            }
            8 => {
                return v___x_6748_;
            }
            9 => {
                if v_isShared_6755_ == 0 {
                    v___x_6757_ = v___x_6754_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6758_, 0, v_a_6752_);
                    v___x_6757_ = v_reuseFailAlloc_6758_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(
    mut v_toProcessingContext_6760_: *mut leanh::LeanObject,
    mut v_setupImports_6761_: *mut leanh::LeanObject,
    mut v_old_x3f_6762_: *mut leanh::LeanObject,
    mut v___f_6763_: *mut leanh::LeanObject,
    mut v___y_6764_: *mut leanh::LeanObject,
    mut v___y_6765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6766_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(
        v_toProcessingContext_6760_,
        v_setupImports_6761_,
        v_old_x3f_6762_,
        v___f_6763_,
        v___y_6764_,
    );
    leanh::lean_dec_ref(v___y_6764_);
    return v_res_6766_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(
    mut v___x_6767_: *mut leanh::LeanObject,
    mut v_toProcessingContext_6768_: *mut leanh::LeanObject,
    mut v_x_6769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6770_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_6767_);
    v___x_6771_ = leanh::lean_box(0);
    v___x_6772_ = leanh::lean_box(0);
    v___x_6773_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_6773_, 0, v_x_6769_);
    leanh::lean_ctor_set(v___x_6773_, 1, v___x_6770_);
    leanh::lean_ctor_set(v___x_6773_, 2, v_toProcessingContext_6768_);
    leanh::lean_ctor_set(v___x_6773_, 3, v___x_6771_);
    leanh::lean_ctor_set(v___x_6773_, 4, v___x_6772_);
    return v___x_6773_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(
    mut v_setupImports_6774_: *mut leanh::LeanObject,
    mut v_old_x3f_6775_: *mut leanh::LeanObject,
    mut v_a_6776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toProcessingContext_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toProcessingContext_6778_ = leanh::lean_ctor_get(v_a_6776_, 0);
    v___x_6779_ = l_Lean_Language_instInhabitedSnapshotLeaf;
    leanh::lean_inc_ref(v_a_6776_);
    leanh::lean_inc_ref_n(v_toProcessingContext_6778_, 3);
    v___f_6780_ = leanh::lean_alloc_closure(
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed
            as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_6780_, 0, v_toProcessingContext_6778_);
    leanh::lean_closure_set(v___f_6780_, 1, v_a_6776_);
    leanh::lean_inc(v_old_x3f_6775_);
    v___f_6781_ = leanh::lean_alloc_closure(
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed
            as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___f_6781_, 0, v_toProcessingContext_6778_);
    leanh::lean_closure_set(v___f_6781_, 1, v_setupImports_6774_);
    leanh::lean_closure_set(v___f_6781_, 2, v_old_x3f_6775_);
    leanh::lean_closure_set(v___f_6781_, 3, v___f_6780_);
    v___f_6782_ = leanh::lean_alloc_closure(
        l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_6782_, 0, v___x_6779_);
    leanh::lean_closure_set(v___f_6782_, 1, v_toProcessingContext_6778_);
    if leanh::lean_obj_tag(v_old_x3f_6775_) == 1 {
        let mut v_val_6783_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_result_x3f_6784_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6783_ = leanh::lean_ctor_get(v_old_x3f_6775_, 0);
        leanh::lean_inc(v_val_6783_);
        leanh::lean_dec_ref_known(v_old_x3f_6775_, 1);
        v_result_x3f_6784_ = leanh::lean_ctor_get(v_val_6783_, 4);
        if leanh::lean_obj_tag(v_result_x3f_6784_) == 1 {
            let mut v_stx_6785_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_6786_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6788_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_stx_6785_ = leanh::lean_ctor_get(v_val_6783_, 3);
            leanh::lean_inc(v_stx_6785_);
            v_val_6786_ = leanh::lean_ctor_get(v_result_x3f_6784_, 0);
            leanh::lean_inc(v_val_6783_);
            v___x_6787_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_6783_);
            v___x_6788_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_6787_);
            if leanh::lean_obj_tag(v___x_6788_) == 1 {
                let mut v_val_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_val_6789_ = leanh::lean_ctor_get(v___x_6788_, 0);
                leanh::lean_inc(v_val_6789_);
                leanh::lean_dec_ref_known(v___x_6788_, 1);
                if leanh::lean_obj_tag(v_val_6789_) == 1 {
                    let mut v_val_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_firstCmdSnap_6791_: *mut leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v___x_6792_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v_val_6790_ = leanh::lean_ctor_get(v_val_6789_, 0);
                    leanh::lean_inc(v_val_6790_);
                    leanh::lean_dec_ref_known(v_val_6789_, 1);
                    v_firstCmdSnap_6791_ = leanh::lean_ctor_get(v_val_6790_, 1);
                    leanh::lean_inc_ref(v_firstCmdSnap_6791_);
                    leanh::lean_dec(v_val_6790_);
                    v___x_6792_ =
                        l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_6791_);
                    if leanh::lean_obj_tag(v___x_6792_) == 1 {
                        let mut v_val_6793_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_nextCmdSnap_x3f_6794_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        v_val_6793_ = leanh::lean_ctor_get(v___x_6792_, 0);
                        leanh::lean_inc(v_val_6793_);
                        leanh::lean_dec_ref_known(v___x_6792_, 1);
                        v_nextCmdSnap_x3f_6794_ = leanh::lean_ctor_get(v_val_6793_, 4);
                        leanh::lean_inc(v_nextCmdSnap_x3f_6794_);
                        leanh::lean_dec(v_val_6793_);
                        if leanh::lean_obj_tag(v_nextCmdSnap_x3f_6794_) == 0 {
                            let mut v___x_6795_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v_stx_6785_);
                            leanh::lean_dec(v_val_6783_);
                            v___x_6795_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_6782_, v___f_6781_, v_a_6776_);
                            return v___x_6795_;
                        } else {
                            let mut v_val_6796_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6797_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            v_val_6796_ = leanh::lean_ctor_get(v_nextCmdSnap_x3f_6794_, 0);
                            leanh::lean_inc(v_val_6796_);
                            leanh::lean_dec_ref_known(v_nextCmdSnap_x3f_6794_, 1);
                            v___x_6797_ =
                                l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_6796_);
                            if leanh::lean_obj_tag(v___x_6797_) == 1 {
                                let mut v_val_6798_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v_parserState_6799_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v_pos_6800_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_6801_: u8 = 0;
                                v_val_6798_ = leanh::lean_ctor_get(v___x_6797_, 0);
                                leanh::lean_inc(v_val_6798_);
                                leanh::lean_dec_ref_known(v___x_6797_, 1);
                                v_parserState_6799_ = leanh::lean_ctor_get(v_val_6798_, 2);
                                leanh::lean_inc_ref(v_parserState_6799_);
                                leanh::lean_dec(v_val_6798_);
                                v_pos_6800_ = leanh::lean_ctor_get(v_parserState_6799_, 0);
                                leanh::lean_inc(v_pos_6800_);
                                leanh::lean_dec_ref(v_parserState_6799_);
                                v___x_6801_ =
                                    l_Lean_Language_Lean_isBeforeEditPos(v_pos_6800_, v_a_6776_);
                                leanh::lean_dec(v_pos_6800_);
                                if v___x_6801_ == 0 {
                                    let mut v___x_6802_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    leanh::lean_dec(v_stx_6785_);
                                    leanh::lean_dec(v_val_6783_);
                                    v___x_6802_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_6782_, v___f_6781_, v_a_6776_);
                                    return v___x_6802_;
                                } else {
                                    let mut v_parserState_6803_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_6804_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    leanh::lean_dec_ref(v___f_6782_);
                                    leanh::lean_dec_ref(v___f_6781_);
                                    v_parserState_6803_ =
                                        leanh::lean_ctor_get(v_val_6786_, 0);
                                    leanh::lean_inc_ref(v_parserState_6803_);
                                    leanh::lean_inc_ref(v_toProcessingContext_6778_);
                                    v___x_6804_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_6778_, v_a_6776_, v_val_6783_, v_stx_6785_, v_parserState_6803_, v_a_6776_);
                                    return v___x_6804_;
                                }
                            } else {
                                let mut v___x_6805_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                leanh::lean_dec(v___x_6797_);
                                leanh::lean_dec(v_stx_6785_);
                                leanh::lean_dec(v_val_6783_);
                                v___x_6805_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_6782_, v___f_6781_, v_a_6776_);
                                return v___x_6805_;
                            }
                        }
                    } else {
                        let mut v___x_6806_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v___x_6792_);
                        leanh::lean_dec(v_stx_6785_);
                        leanh::lean_dec(v_val_6783_);
                        v___x_6806_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_6782_, v___f_6781_, v_a_6776_);
                        return v___x_6806_;
                    }
                } else {
                    let mut v___x_6807_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_val_6789_);
                    leanh::lean_dec(v_stx_6785_);
                    leanh::lean_dec(v_val_6783_);
                    v___x_6807_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_6782_, v___f_6781_, v_a_6776_);
                    return v___x_6807_;
                }
            } else {
                let mut v___x_6808_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_6788_);
                leanh::lean_dec(v_stx_6785_);
                leanh::lean_dec(v_val_6783_);
                v___x_6808_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_6782_, v___f_6781_, v_a_6776_);
                return v___x_6808_;
            }
        } else {
            let mut v___x_6809_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_6783_);
            v___x_6809_ =
                l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(
                    v___f_6782_,
                    v___f_6781_,
                    v_a_6776_,
                );
            return v___x_6809_;
        }
    } else {
        let mut v___x_6810_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_old_x3f_6775_);
        v___x_6810_ =
            l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(
                v___f_6782_,
                v___f_6781_,
                v_a_6776_,
            );
        return v___x_6810_;
    }
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(
    mut v_setupImports_6811_: *mut leanh::LeanObject,
    mut v_old_x3f_6812_: *mut leanh::LeanObject,
    mut v_a_6813_: *mut leanh::LeanObject,
    mut v_a_6814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6815_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(
        v_setupImports_6811_,
        v_old_x3f_6812_,
        v_a_6813_,
    );
    leanh::lean_dec_ref(v_a_6813_);
    return v_res_6815_;
}
pub unsafe fn l_Lean_Language_Lean_process(
    mut v_setupImports_6816_: *mut leanh::LeanObject,
    mut v_old_x3f_6817_: *mut leanh::LeanObject,
    mut v_a_6818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6826_: u8 = 0;
    let mut v_ictx_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6832_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_old_x3f_6817_);
                v___x_6820_ = leanh::lean_alloc_closure(
                    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___x_6820_, 0, v_setupImports_6816_);
                leanh::lean_closure_set(v___x_6820_, 1, v_old_x3f_6817_);
                if leanh::lean_obj_tag(v_old_x3f_6817_) == 0 {
                    v___x_6821_ = leanh::lean_box(0);
                    v___x_6822_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(
                        v___x_6820_,
                        v___x_6821_,
                        v_a_6818_,
                    );
                    return v___x_6822_;
                } else {
                    v_val_6823_ = leanh::lean_ctor_get(v_old_x3f_6817_, 0);
                    v_isSharedCheck_6832_ =
                        (!leanh::lean_is_exclusive(v_old_x3f_6817_)) as u8;
                    if v_isSharedCheck_6832_ == 0 {
                        v___x_6825_ = v_old_x3f_6817_;
                        v_isShared_6826_ = v_isSharedCheck_6832_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6823_);
                        leanh::lean_dec(v_old_x3f_6817_);
                        v___x_6825_ = leanh::lean_box(0);
                        v_isShared_6826_ = v_isSharedCheck_6832_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_ictx_6827_ = leanh::lean_ctor_get(v_val_6823_, 2);
                leanh::lean_inc_ref(v_ictx_6827_);
                leanh::lean_dec(v_val_6823_);
                if v_isShared_6826_ == 0 {
                    leanh::lean_ctor_set(v___x_6825_, 0, v_ictx_6827_);
                    v___x_6829_ = v___x_6825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6831_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6831_, 0, v_ictx_6827_);
                    v___x_6829_ = v_reuseFailAlloc_6831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6830_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(
                    v___x_6820_,
                    v___x_6829_,
                    v_a_6818_,
                );
                return v___x_6830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_Lean_process___boxed(
    mut v_setupImports_6833_: *mut leanh::LeanObject,
    mut v_old_x3f_6834_: *mut leanh::LeanObject,
    mut v_a_6835_: *mut leanh::LeanObject,
    mut v_a_6836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6837_ = l_Lean_Language_Lean_process(v_setupImports_6833_, v_old_x3f_6834_, v_a_6835_);
    leanh::lean_dec_ref(v_a_6835_);
    return v_res_6837_;
}
pub unsafe fn l_Lean_Language_Lean_processCommands(
    mut v_inputCtx_6838_: *mut leanh::LeanObject,
    mut v_parserState_6839_: *mut leanh::LeanObject,
    mut v_commandState_6840_: *mut leanh::LeanObject,
    mut v_old_x3f_6841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: u8 = 0;
    let mut v___x_6853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6859_: u8 = 0;
    let mut v_fst_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6864_: u8 = 0;
    let mut v___x_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6843_ = lean_io_promise_new();
                v___x_6844_ = l_IO_CancelToken_new();
                if leanh::lean_obj_tag(v_old_x3f_6841_) == 0 {
                    v___x_6865_ = leanh::lean_box(0);
                    v___y_6851_ = v___x_6865_;
                    state = 2;
                    continue;
                } else {
                    v_val_6866_ = leanh::lean_ctor_get(v_old_x3f_6841_, 0);
                    v_snd_6867_ = leanh::lean_ctor_get(v_val_6866_, 1);
                    leanh::lean_inc(v_snd_6867_);
                    v___x_6868_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6868_, 0, v_snd_6867_);
                    v___y_6851_ = v___x_6868_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_6848_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(
                    v___y_6846_,
                    v___y_6847_,
                    v_inputCtx_6838_,
                );
                leanh::lean_dec(v___x_6848_);
                v___x_6849_ = l_IO_Promise_result_x21___redArg(v___x_6843_);
                leanh::lean_dec(v___x_6843_);
                return v___x_6849_;
            }
            2 => {
                v___x_6852_ = 1;
                v___x_6853_ = leanh::lean_box((v___x_6852_) as usize);
                leanh::lean_inc(v___x_6843_);
                v___x_6854_ = leanh::lean_alloc_closure(
                    l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed
                        as *mut core::ffi::c_void,
                    8,
                    6,
                );
                leanh::lean_closure_set(v___x_6854_, 0, v___y_6851_);
                leanh::lean_closure_set(v___x_6854_, 1, v_parserState_6839_);
                leanh::lean_closure_set(v___x_6854_, 2, v_commandState_6840_);
                leanh::lean_closure_set(v___x_6854_, 3, v___x_6843_);
                leanh::lean_closure_set(v___x_6854_, 4, v___x_6853_);
                leanh::lean_closure_set(v___x_6854_, 5, v___x_6844_);
                if leanh::lean_obj_tag(v_old_x3f_6841_) == 0 {
                    v___x_6855_ = leanh::lean_box(0);
                    v___y_6846_ = v___x_6854_;
                    v___y_6847_ = v___x_6855_;
                    state = 1;
                    continue;
                } else {
                    v_val_6856_ = leanh::lean_ctor_get(v_old_x3f_6841_, 0);
                    v_isSharedCheck_6864_ =
                        (!leanh::lean_is_exclusive(v_old_x3f_6841_)) as u8;
                    if v_isSharedCheck_6864_ == 0 {
                        v___x_6858_ = v_old_x3f_6841_;
                        v_isShared_6859_ = v_isSharedCheck_6864_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6856_);
                        leanh::lean_dec(v_old_x3f_6841_);
                        v___x_6858_ = leanh::lean_box(0);
                        v_isShared_6859_ = v_isSharedCheck_6864_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_6860_ = leanh::lean_ctor_get(v_val_6856_, 0);
                leanh::lean_inc(v_fst_6860_);
                leanh::lean_dec(v_val_6856_);
                if v_isShared_6859_ == 0 {
                    leanh::lean_ctor_set(v___x_6858_, 0, v_fst_6860_);
                    v___x_6862_ = v___x_6858_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6863_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6863_, 0, v_fst_6860_);
                    v___x_6862_ = v_reuseFailAlloc_6863_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_6846_ = v___x_6854_;
                v___y_6847_ = v___x_6862_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_Lean_processCommands___boxed(
    mut v_inputCtx_6869_: *mut leanh::LeanObject,
    mut v_parserState_6870_: *mut leanh::LeanObject,
    mut v_commandState_6871_: *mut leanh::LeanObject,
    mut v_old_x3f_6872_: *mut leanh::LeanObject,
    mut v_a_6873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6874_ = l_Lean_Language_Lean_processCommands(
        v_inputCtx_6869_,
        v_parserState_6870_,
        v_commandState_6871_,
        v_old_x3f_6872_,
    );
    leanh::lean_dec_ref(v_inputCtx_6869_);
    return v_res_6874_;
}
pub unsafe fn l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(
    mut v_snap_6875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nextCmdSnap_x3f_6876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elabSnap_6880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultSnap_6881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdState_6883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_nextCmdSnap_x3f_6876_ = leanh::lean_ctor_get(v_snap_6875_, 4);
                if leanh::lean_obj_tag(v_nextCmdSnap_x3f_6876_) == 1 {
                    leanh::lean_inc_ref(v_nextCmdSnap_x3f_6876_);
                    leanh::lean_dec_ref(v_snap_6875_);
                    v_val_6877_ = leanh::lean_ctor_get(v_nextCmdSnap_x3f_6876_, 0);
                    leanh::lean_inc(v_val_6877_);
                    leanh::lean_dec_ref_known(v_nextCmdSnap_x3f_6876_, 1);
                    v___x_6878_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_6877_);
                    v_snap_6875_ = v___x_6878_;
                    state = 0;
                    continue;
                } else {
                    v_elabSnap_6880_ = leanh::lean_ctor_get(v_snap_6875_, 3);
                    leanh::lean_inc_ref(v_elabSnap_6880_);
                    leanh::lean_dec_ref(v_snap_6875_);
                    v_resultSnap_6881_ = leanh::lean_ctor_get(v_elabSnap_6880_, 2);
                    leanh::lean_inc_ref(v_resultSnap_6881_);
                    leanh::lean_dec_ref(v_elabSnap_6880_);
                    v___x_6882_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_6881_);
                    v_cmdState_6883_ = leanh::lean_ctor_get(v___x_6882_, 1);
                    leanh::lean_inc_ref(v_cmdState_6883_);
                    leanh::lean_dec(v___x_6882_);
                    v___x_6884_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6884_, 0, v_cmdState_6883_);
                    return v___x_6884_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_Lean_waitForFinalCmdState_x3f(
    mut v_snap_6885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_result_x3f_6886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_result_x3f_6886_ = leanh::lean_ctor_get(v_snap_6885_, 4);
    leanh::lean_inc(v_result_x3f_6886_);
    leanh::lean_dec_ref(v_snap_6885_);
    if leanh::lean_obj_tag(v_result_x3f_6886_) == 0 {
        let mut v___x_6887_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6887_ = leanh::lean_box(0);
        return v___x_6887_;
    } else {
        let mut v_val_6888_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_processedSnap_6889_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_result_x3f_6891_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6888_ = leanh::lean_ctor_get(v_result_x3f_6886_, 0);
        leanh::lean_inc(v_val_6888_);
        leanh::lean_dec_ref_known(v_result_x3f_6886_, 1);
        v_processedSnap_6889_ = leanh::lean_ctor_get(v_val_6888_, 1);
        leanh::lean_inc_ref(v_processedSnap_6889_);
        leanh::lean_dec(v_val_6888_);
        v___x_6890_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_6889_);
        v_result_x3f_6891_ = leanh::lean_ctor_get(v___x_6890_, 2);
        leanh::lean_inc(v_result_x3f_6891_);
        leanh::lean_dec(v___x_6890_);
        if leanh::lean_obj_tag(v_result_x3f_6891_) == 0 {
            let mut v___x_6892_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6892_ = leanh::lean_box(0);
            return v___x_6892_;
        } else {
            let mut v_val_6893_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_firstCmdSnap_6894_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6896_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_6893_ = leanh::lean_ctor_get(v_result_x3f_6891_, 0);
            leanh::lean_inc(v_val_6893_);
            leanh::lean_dec_ref_known(v_result_x3f_6891_, 1);
            v_firstCmdSnap_6894_ = leanh::lean_ctor_get(v_val_6893_, 1);
            leanh::lean_inc_ref(v_firstCmdSnap_6894_);
            leanh::lean_dec(v_val_6893_);
            v___x_6895_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_6894_);
            v___x_6896_ =
                l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(
                    v___x_6895_,
                );
            return v___x_6896_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Language_Lean(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Language_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Language_Lean_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Import(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Language_Lean_experimental_module = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Language_Lean_experimental_module);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Language_Lean(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Language_Lean(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Language_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Language_Lean_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Import(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Language_Lean(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Language_Lean(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Language_Lean(builtin);
}