// Lean compiler output
// Module: Lean.Elab.Frontend
// Imports: Lean.Language.Lean Lean.Server.References Lean.Util.Profiler Lean.Compiler.Options Lean.Linter.PersistentLintLog Lean.Util.ProfilerServer
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::GetElem::l_List_get_x21Internal___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_firstFrontendMacroScope};
use crate::r#gen::Init::System::IO::l_IO_FS_writeFile;
use crate::r#gen::Lean::Compiler::Options::{
    initialize_Lean_Compiler_Options, l_Lean_Compiler_compiler_postponeCompile,
    runtime_initialize_Lean_Compiler_Options,
};
use crate::r#gen::Lean::CoreM::{l_Lean_Elab_async, l_Lean_internal_cmdlineSnapshots};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_mergeBy;
use crate::r#gen::Lean::Data::PersistentArray::l_Array_toPArray_x27___redArg;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_elabCommandTopLevel, l_Lean_Elab_Command_mkState,
};
use crate::r#gen::Lean::Elab::Import::{
    l_Lean_Elab_HeaderSyntax_imports, l_Lean_Elab_HeaderSyntax_isModule,
};
use crate::r#gen::Lean::Environment::{l_Lean_Environment_displayStats, l_Lean_writeModule};
use crate::r#gen::Lean::Exception::l_Lean_Exception_toMessageData;
use crate::r#gen::Lean::Language::Basic::{
    l_Lean_Language_SnapshotTask_get___redArg, l_Lean_Language_SnapshotTask_map___redArg,
    l_Lean_Language_SnapshotTree_getAll, l_Lean_Language_SnapshotTree_runAndReport,
};
use crate::r#gen::Lean::Language::Lean::Types::{
    l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go,
    l_Lean_Language_Lean_pushOpt___redArg,
};
use crate::r#gen::Lean::Language::Lean::{
    initialize_Lean_Language_Lean, l_Lean_Language_Lean_process,
    l_Lean_Language_Lean_processCommands, l_Lean_Language_Lean_waitForFinalCmdState_x3f,
    runtime_initialize_Lean_Language_Lean,
};
use crate::r#gen::Lean::Linter::PersistentLintLog::{
    initialize_Lean_Linter_PersistentLintLog, l_Lean_Linter_recordLints,
    runtime_initialize_Lean_Linter_PersistentLintLog,
};
use crate::r#gen::Lean::LoadDynlib::lean_load_dynlib;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_toString, l_Lean_MessageLog_append, l_Lean_MessageLog_empty,
};
use crate::r#gen::Lean::Parser::Extension::l_Lean_Parser_mkInputContext___redArg;
use crate::r#gen::Lean::Parser::Module::{
    l_Lean_Parser_isTerminalCommand, l_Lean_Parser_parseCommand,
};
use crate::r#gen::Lean::Server::References::{
    initialize_Lean_Server_References, l_Lean_Server_ModuleRefs_toLspModuleRefs,
    l_Lean_Server_collectImports, l_Lean_Server_findModuleRefs,
    l_Lean_Server_instToJsonIlean_toJson, runtime_initialize_Lean_Server_References,
};
use crate::r#gen::Lean::Util::LeanOptions::l_Lean_LeanOptions_toOptions;
use crate::r#gen::Lean::Util::Profile::l_Lean_profileitIOUnsafe___redArg;
use crate::r#gen::Lean::Util::Profiler::{
    initialize_Lean_Util_Profiler, l_Lean_Firefox_Profile_export,
    l_Lean_Firefox_instToJsonProfile_toJson, runtime_initialize_Lean_Util_Profiler,
};
use crate::r#gen::Lean::Util::ProfilerServer::{
    initialize_Lean_Util_ProfilerServer, l_Lean_Firefox_Profile_serve,
    runtime_initialize_Lean_Util_ProfilerServer,
};
use crate::r#gen::Lean::Util::Trace::{l_Lean_trace_profiler_output, l_Lean_trace_profiler_serve};
use crate::lean_imports_rs::Init::Core::{lean_strict_or, lean_task_get_own};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Float::lean_float_div;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_string_utf8_byte_size, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{lean_io_mono_nanos_now, lean_runtime_forget};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Util::Profile::lean_profileit;
pub static l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 110, 116, 101, 114, 110, 97, 108,
        32, 101, 114, 114, 111, 114, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Frontend_processCommand___closed__0_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [112, 97, 114, 115, 105, 110, 103, 0],
};
static mut l_Lean_Elab_Frontend_processCommand___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Frontend_processCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_IO_processCommandsIncrementally___closed__0_value:
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
static mut l_Lean_Elab_IO_processCommandsIncrementally___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_IO_processCommandsIncrementally___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_process___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            256 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_process___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_process___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_process___closed__1_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [60, 105, 110, 112, 117, 116, 62, 0],
    };
static mut l_Lean_Elab_process___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_process___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_runFrontend___lam__2___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_runFrontend___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_runFrontend___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_runFrontend___lam__5___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_runFrontend___lam__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_runFrontend___lam__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_runFrontend___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_runFrontend___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_runFrontend___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_runFrontend___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_runFrontend___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_runFrontend___lam__2 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_runFrontend___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_runFrontend___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_runFrontend___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_runFrontend___closed__2: f64 = 0.0;
pub static l_Lean_Elab_runFrontend___closed__3_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            46, 111, 108, 101, 97, 110, 32, 115, 101, 114, 105, 97, 108, 105, 122, 97, 116, 105,
            111, 110, 0,
        ],
    };
static mut l_Lean_Elab_runFrontend___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_runFrontend___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_runFrontend___closed__4_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_runFrontend___lam__5 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_runFrontend___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_runFrontend___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_runFrontend___closed__4_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Frontend_setCommandState___redArg(
    mut v_commandState_1346_: *mut crate::leanh::LeanObject,
    mut v_a_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserState_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commands_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1355_: u8 = 0;
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut v_unused_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1349_ = lean_st_ref_take(v_a_1347_);
                v_parserState_1350_ = crate::leanh::lean_ctor_get(v___x_1349_, 1);
                v_cmdPos_1351_ = crate::leanh::lean_ctor_get(v___x_1349_, 2);
                v_commands_1352_ = crate::leanh::lean_ctor_get(v___x_1349_, 3);
                v_isSharedCheck_1362_ = (!crate::leanh::lean_is_exclusive(v___x_1349_)) as u8;
                if v_isSharedCheck_1362_ == 0 {
                    v_unused_1363_ = crate::leanh::lean_ctor_get(v___x_1349_, 0);
                    crate::leanh::lean_dec(v_unused_1363_);
                    v___x_1354_ = v___x_1349_;
                    v_isShared_1355_ = v_isSharedCheck_1362_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_commands_1352_);
                    crate::leanh::lean_inc(v_cmdPos_1351_);
                    crate::leanh::lean_inc(v_parserState_1350_);
                    crate::leanh::lean_dec(v___x_1349_);
                    v___x_1354_ = crate::leanh::lean_box(0);
                    v_isShared_1355_ = v_isSharedCheck_1362_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1355_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1354_, 0, v_commandState_1346_);
                    v___x_1357_ = v___x_1354_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1361_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_commandState_1346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_parserState_1350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_cmdPos_1351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_commands_1352_);
                    v___x_1357_ = v_reuseFailAlloc_1361_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1358_ = lean_st_ref_set(v_a_1347_, v___x_1357_);
                v___x_1359_ = crate::leanh::lean_box(0);
                v___x_1360_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1360_, 0, v___x_1359_);
                return v___x_1360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Frontend_setCommandState___redArg___boxed(
    mut v_commandState_1364_: *mut crate::leanh::LeanObject,
    mut v_a_1365_: *mut crate::leanh::LeanObject,
    mut v_a_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_Lean_Elab_Frontend_setCommandState___redArg(v_commandState_1364_, v_a_1365_);
    crate::leanh::lean_dec(v_a_1365_);
    return v_res_1367_;
}
pub unsafe fn l_Lean_Elab_Frontend_setCommandState(
    mut v_commandState_1368_: *mut crate::leanh::LeanObject,
    mut v_a_1369_: *mut crate::leanh::LeanObject,
    mut v_a_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = l_Lean_Elab_Frontend_setCommandState___redArg(v_commandState_1368_, v_a_1370_);
    return v___x_1372_;
}
pub unsafe fn l_Lean_Elab_Frontend_setCommandState___boxed(
    mut v_commandState_1373_: *mut crate::leanh::LeanObject,
    mut v_a_1374_: *mut crate::leanh::LeanObject,
    mut v_a_1375_: *mut crate::leanh::LeanObject,
    mut v_a_1376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1377_ = l_Lean_Elab_Frontend_setCommandState(v_commandState_1373_, v_a_1374_, v_a_1375_);
    crate::leanh::lean_dec(v_a_1375_);
    crate::leanh::lean_dec_ref(v_a_1374_);
    return v_res_1377_;
}
pub unsafe fn l_Lean_Elab_Frontend_runCommandElabM___redArg(
    mut v_x_1379_: *mut crate::leanh::LeanObject,
    mut v_a_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commandState_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1402_: u8 = 0;
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v_unused_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1383_ = lean_st_ref_get(v_a_1381_);
                v_commandState_1384_ = crate::leanh::lean_ctor_get(v___x_1383_, 0);
                crate::leanh::lean_inc_ref(v_commandState_1384_);
                v_cmdPos_1385_ = crate::leanh::lean_ctor_get(v___x_1383_, 2);
                crate::leanh::lean_inc(v_cmdPos_1385_);
                crate::leanh::lean_dec(v___x_1383_);
                v___x_1386_ = lean_st_mk_ref(v_commandState_1384_);
                v_fileName_1387_ = crate::leanh::lean_ctor_get(v_a_1380_, 1);
                v_fileMap_1388_ = crate::leanh::lean_ctor_get(v_a_1380_, 2);
                v___x_1389_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1390_ = crate::leanh::lean_box(0);
                v___x_1391_ = crate::leanh::lean_box(0);
                v___x_1392_ = l_Lean_firstFrontendMacroScope;
                v___x_1393_ = crate::leanh::lean_box(0);
                v___x_1394_ = 0;
                crate::leanh::lean_inc_ref(v_fileMap_1388_);
                crate::leanh::lean_inc_ref(v_fileName_1387_);
                v___x_1395_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1395_, 0, v_fileName_1387_);
                crate::leanh::lean_ctor_set(v___x_1395_, 1, v_fileMap_1388_);
                crate::leanh::lean_ctor_set(v___x_1395_, 2, v___x_1389_);
                crate::leanh::lean_ctor_set(v___x_1395_, 3, v_cmdPos_1385_);
                crate::leanh::lean_ctor_set(v___x_1395_, 4, v___x_1390_);
                crate::leanh::lean_ctor_set(v___x_1395_, 5, v___x_1391_);
                crate::leanh::lean_ctor_set(v___x_1395_, 6, v___x_1392_);
                crate::leanh::lean_ctor_set(v___x_1395_, 7, v___x_1393_);
                crate::leanh::lean_ctor_set(v___x_1395_, 8, v___x_1391_);
                crate::leanh::lean_ctor_set(v___x_1395_, 9, v___x_1391_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1395_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    v___x_1394_,
                );
                crate::leanh::lean_inc(v___x_1386_);
                v___x_1396_ = crate::leanh::lean_apply_3(
                    v_x_1379_,
                    v___x_1395_,
                    v___x_1386_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1396_) == 0 {
                    v_a_1397_ = crate::leanh::lean_ctor_get(v___x_1396_, 0);
                    crate::leanh::lean_inc(v_a_1397_);
                    crate::leanh::lean_dec_ref_known(v___x_1396_, 1);
                    v___x_1398_ = lean_st_ref_get(v___x_1386_);
                    crate::leanh::lean_dec(v___x_1386_);
                    v___x_1399_ =
                        l_Lean_Elab_Frontend_setCommandState___redArg(v___x_1398_, v_a_1381_);
                    v_isSharedCheck_1406_ = (!crate::leanh::lean_is_exclusive(v___x_1399_)) as u8;
                    if v_isSharedCheck_1406_ == 0 {
                        v_unused_1407_ = crate::leanh::lean_ctor_get(v___x_1399_, 0);
                        crate::leanh::lean_dec(v_unused_1407_);
                        v___x_1401_ = v___x_1399_;
                        v_isShared_1402_ = v_isSharedCheck_1406_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1399_);
                        v___x_1401_ = crate::leanh::lean_box(0);
                        v_isShared_1402_ = v_isSharedCheck_1406_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1386_);
                    v_a_1408_ = crate::leanh::lean_ctor_get(v___x_1396_, 0);
                    v_isSharedCheck_1420_ = (!crate::leanh::lean_is_exclusive(v___x_1396_)) as u8;
                    if v_isSharedCheck_1420_ == 0 {
                        v___x_1410_ = v___x_1396_;
                        v_isShared_1411_ = v_isSharedCheck_1420_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1408_);
                        crate::leanh::lean_dec(v___x_1396_);
                        v___x_1410_ = crate::leanh::lean_box(0);
                        v_isShared_1411_ = v_isSharedCheck_1420_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1402_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1401_, 0, v_a_1397_);
                    v___x_1404_ = v___x_1401_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1397_);
                    v___x_1404_ = v_reuseFailAlloc_1405_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1404_;
            }
            3 => {
                v___x_1412_ = l_Lean_Exception_toMessageData(v_a_1408_);
                v___x_1413_ = l_Lean_MessageData_toString(v___x_1412_);
                v___x_1414_ = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
                v___x_1415_ = lean_string_append(v___x_1414_, v___x_1413_);
                crate::leanh::lean_dec_ref(v___x_1413_);
                v___x_1416_ = crate::leanh::lean_alloc_ctor(18, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1416_, 0, v___x_1415_);
                if v_isShared_1411_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1410_, 0, v___x_1416_);
                    v___x_1418_ = v___x_1410_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
                    v___x_1418_ = v_reuseFailAlloc_1419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Frontend_runCommandElabM___redArg___boxed(
    mut v_x_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
    mut v_a_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1425_ = l_Lean_Elab_Frontend_runCommandElabM___redArg(v_x_1421_, v_a_1422_, v_a_1423_);
    crate::leanh::lean_dec(v_a_1423_);
    crate::leanh::lean_dec_ref(v_a_1422_);
    return v_res_1425_;
}
pub unsafe fn l_Lean_Elab_Frontend_runCommandElabM(
    mut v_00_u03b1_1426_: *mut crate::leanh::LeanObject,
    mut v_x_1427_: *mut crate::leanh::LeanObject,
    mut v_a_1428_: *mut crate::leanh::LeanObject,
    mut v_a_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commandState_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: u8 = 0;
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1450_: u8 = 0;
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1454_: u8 = 0;
    let mut v_unused_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1459_: u8 = 0;
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1431_ = lean_st_ref_get(v_a_1429_);
                v_commandState_1432_ = crate::leanh::lean_ctor_get(v___x_1431_, 0);
                crate::leanh::lean_inc_ref(v_commandState_1432_);
                v_cmdPos_1433_ = crate::leanh::lean_ctor_get(v___x_1431_, 2);
                crate::leanh::lean_inc(v_cmdPos_1433_);
                crate::leanh::lean_dec(v___x_1431_);
                v___x_1434_ = lean_st_mk_ref(v_commandState_1432_);
                v_fileName_1435_ = crate::leanh::lean_ctor_get(v_a_1428_, 1);
                v_fileMap_1436_ = crate::leanh::lean_ctor_get(v_a_1428_, 2);
                v___x_1437_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1438_ = crate::leanh::lean_box(0);
                v___x_1439_ = crate::leanh::lean_box(0);
                v___x_1440_ = l_Lean_firstFrontendMacroScope;
                v___x_1441_ = crate::leanh::lean_box(0);
                v___x_1442_ = 0;
                crate::leanh::lean_inc_ref(v_fileMap_1436_);
                crate::leanh::lean_inc_ref(v_fileName_1435_);
                v___x_1443_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1443_, 0, v_fileName_1435_);
                crate::leanh::lean_ctor_set(v___x_1443_, 1, v_fileMap_1436_);
                crate::leanh::lean_ctor_set(v___x_1443_, 2, v___x_1437_);
                crate::leanh::lean_ctor_set(v___x_1443_, 3, v_cmdPos_1433_);
                crate::leanh::lean_ctor_set(v___x_1443_, 4, v___x_1438_);
                crate::leanh::lean_ctor_set(v___x_1443_, 5, v___x_1439_);
                crate::leanh::lean_ctor_set(v___x_1443_, 6, v___x_1440_);
                crate::leanh::lean_ctor_set(v___x_1443_, 7, v___x_1441_);
                crate::leanh::lean_ctor_set(v___x_1443_, 8, v___x_1439_);
                crate::leanh::lean_ctor_set(v___x_1443_, 9, v___x_1439_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1443_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    v___x_1442_,
                );
                crate::leanh::lean_inc(v___x_1434_);
                v___x_1444_ = crate::leanh::lean_apply_3(
                    v_x_1427_,
                    v___x_1443_,
                    v___x_1434_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1444_) == 0 {
                    v_a_1445_ = crate::leanh::lean_ctor_get(v___x_1444_, 0);
                    crate::leanh::lean_inc(v_a_1445_);
                    crate::leanh::lean_dec_ref_known(v___x_1444_, 1);
                    v___x_1446_ = lean_st_ref_get(v___x_1434_);
                    crate::leanh::lean_dec(v___x_1434_);
                    v___x_1447_ =
                        l_Lean_Elab_Frontend_setCommandState___redArg(v___x_1446_, v_a_1429_);
                    v_isSharedCheck_1454_ = (!crate::leanh::lean_is_exclusive(v___x_1447_)) as u8;
                    if v_isSharedCheck_1454_ == 0 {
                        v_unused_1455_ = crate::leanh::lean_ctor_get(v___x_1447_, 0);
                        crate::leanh::lean_dec(v_unused_1455_);
                        v___x_1449_ = v___x_1447_;
                        v_isShared_1450_ = v_isSharedCheck_1454_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1447_);
                        v___x_1449_ = crate::leanh::lean_box(0);
                        v_isShared_1450_ = v_isSharedCheck_1454_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1434_);
                    v_a_1456_ = crate::leanh::lean_ctor_get(v___x_1444_, 0);
                    v_isSharedCheck_1468_ = (!crate::leanh::lean_is_exclusive(v___x_1444_)) as u8;
                    if v_isSharedCheck_1468_ == 0 {
                        v___x_1458_ = v___x_1444_;
                        v_isShared_1459_ = v_isSharedCheck_1468_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1456_);
                        crate::leanh::lean_dec(v___x_1444_);
                        v___x_1458_ = crate::leanh::lean_box(0);
                        v_isShared_1459_ = v_isSharedCheck_1468_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1449_, 0, v_a_1445_);
                    v___x_1452_ = v___x_1449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1453_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1445_);
                    v___x_1452_ = v_reuseFailAlloc_1453_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1452_;
            }
            3 => {
                v___x_1460_ = l_Lean_Exception_toMessageData(v_a_1456_);
                v___x_1461_ = l_Lean_MessageData_toString(v___x_1460_);
                v___x_1462_ = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
                v___x_1463_ = lean_string_append(v___x_1462_, v___x_1461_);
                crate::leanh::lean_dec_ref(v___x_1461_);
                v___x_1464_ = crate::leanh::lean_alloc_ctor(18, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1464_, 0, v___x_1463_);
                if v_isShared_1459_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1458_, 0, v___x_1464_);
                    v___x_1466_ = v___x_1458_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
                    v___x_1466_ = v_reuseFailAlloc_1467_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Frontend_runCommandElabM___boxed(
    mut v_00_u03b1_1469_: *mut crate::leanh::LeanObject,
    mut v_x_1470_: *mut crate::leanh::LeanObject,
    mut v_a_1471_: *mut crate::leanh::LeanObject,
    mut v_a_1472_: *mut crate::leanh::LeanObject,
    mut v_a_1473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1474_ =
        l_Lean_Elab_Frontend_runCommandElabM(v_00_u03b1_1469_, v_x_1470_, v_a_1471_, v_a_1472_);
    crate::leanh::lean_dec(v_a_1472_);
    crate::leanh::lean_dec_ref(v_a_1471_);
    return v_res_1474_;
}
pub unsafe fn l_Lean_Elab_Frontend_elabCommandAtFrontend(
    mut v_stx_1475_: *mut crate::leanh::LeanObject,
    mut v_a_1476_: *mut crate::leanh::LeanObject,
    mut v_a_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commandState_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1502_: u8 = 0;
    let mut v_unused_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1507_: u8 = 0;
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1479_ = lean_st_ref_get(v_a_1477_);
                v_commandState_1480_ = crate::leanh::lean_ctor_get(v___x_1479_, 0);
                crate::leanh::lean_inc_ref(v_commandState_1480_);
                v_cmdPos_1481_ = crate::leanh::lean_ctor_get(v___x_1479_, 2);
                crate::leanh::lean_inc(v_cmdPos_1481_);
                crate::leanh::lean_dec(v___x_1479_);
                v___x_1482_ = lean_st_mk_ref(v_commandState_1480_);
                v_fileName_1483_ = crate::leanh::lean_ctor_get(v_a_1476_, 1);
                v_fileMap_1484_ = crate::leanh::lean_ctor_get(v_a_1476_, 2);
                v___x_1485_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1486_ = crate::leanh::lean_box(0);
                v___x_1487_ = crate::leanh::lean_box(0);
                v___x_1488_ = l_Lean_firstFrontendMacroScope;
                v___x_1489_ = crate::leanh::lean_box(0);
                v___x_1490_ = 0;
                crate::leanh::lean_inc_ref(v_fileMap_1484_);
                crate::leanh::lean_inc_ref(v_fileName_1483_);
                v___x_1491_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1491_, 0, v_fileName_1483_);
                crate::leanh::lean_ctor_set(v___x_1491_, 1, v_fileMap_1484_);
                crate::leanh::lean_ctor_set(v___x_1491_, 2, v___x_1485_);
                crate::leanh::lean_ctor_set(v___x_1491_, 3, v_cmdPos_1481_);
                crate::leanh::lean_ctor_set(v___x_1491_, 4, v___x_1486_);
                crate::leanh::lean_ctor_set(v___x_1491_, 5, v___x_1487_);
                crate::leanh::lean_ctor_set(v___x_1491_, 6, v___x_1488_);
                crate::leanh::lean_ctor_set(v___x_1491_, 7, v___x_1489_);
                crate::leanh::lean_ctor_set(v___x_1491_, 8, v___x_1487_);
                crate::leanh::lean_ctor_set(v___x_1491_, 9, v___x_1487_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1491_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    v___x_1490_,
                );
                v___x_1492_ =
                    l_Lean_Elab_Command_elabCommandTopLevel(v_stx_1475_, v___x_1491_, v___x_1482_);
                crate::leanh::lean_dec_ref_known(v___x_1491_, 10);
                if crate::leanh::lean_obj_tag(v___x_1492_) == 0 {
                    v_a_1493_ = crate::leanh::lean_ctor_get(v___x_1492_, 0);
                    crate::leanh::lean_inc(v_a_1493_);
                    crate::leanh::lean_dec_ref_known(v___x_1492_, 1);
                    v___x_1494_ = lean_st_ref_get(v___x_1482_);
                    crate::leanh::lean_dec(v___x_1482_);
                    v___x_1495_ =
                        l_Lean_Elab_Frontend_setCommandState___redArg(v___x_1494_, v_a_1477_);
                    v_isSharedCheck_1502_ = (!crate::leanh::lean_is_exclusive(v___x_1495_)) as u8;
                    if v_isSharedCheck_1502_ == 0 {
                        v_unused_1503_ = crate::leanh::lean_ctor_get(v___x_1495_, 0);
                        crate::leanh::lean_dec(v_unused_1503_);
                        v___x_1497_ = v___x_1495_;
                        v_isShared_1498_ = v_isSharedCheck_1502_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1495_);
                        v___x_1497_ = crate::leanh::lean_box(0);
                        v_isShared_1498_ = v_isSharedCheck_1502_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1482_);
                    v_a_1504_ = crate::leanh::lean_ctor_get(v___x_1492_, 0);
                    v_isSharedCheck_1516_ = (!crate::leanh::lean_is_exclusive(v___x_1492_)) as u8;
                    if v_isSharedCheck_1516_ == 0 {
                        v___x_1506_ = v___x_1492_;
                        v_isShared_1507_ = v_isSharedCheck_1516_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1504_);
                        crate::leanh::lean_dec(v___x_1492_);
                        v___x_1506_ = crate::leanh::lean_box(0);
                        v_isShared_1507_ = v_isSharedCheck_1516_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1497_, 0, v_a_1493_);
                    v___x_1500_ = v___x_1497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1501_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1493_);
                    v___x_1500_ = v_reuseFailAlloc_1501_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1500_;
            }
            3 => {
                v___x_1508_ = l_Lean_Exception_toMessageData(v_a_1504_);
                v___x_1509_ = l_Lean_MessageData_toString(v___x_1508_);
                v___x_1510_ = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
                v___x_1511_ = lean_string_append(v___x_1510_, v___x_1509_);
                crate::leanh::lean_dec_ref(v___x_1509_);
                v___x_1512_ = crate::leanh::lean_alloc_ctor(18, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1512_, 0, v___x_1511_);
                if v_isShared_1507_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1506_, 0, v___x_1512_);
                    v___x_1514_ = v___x_1506_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1515_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
                    v___x_1514_ = v_reuseFailAlloc_1515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed(
    mut v_stx_1517_: *mut crate::leanh::LeanObject,
    mut v_a_1518_: *mut crate::leanh::LeanObject,
    mut v_a_1519_: *mut crate::leanh::LeanObject,
    mut v_a_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1521_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_stx_1517_, v_a_1518_, v_a_1519_);
    crate::leanh::lean_dec(v_a_1519_);
    crate::leanh::lean_dec_ref(v_a_1518_);
    return v_res_1521_;
}
pub unsafe fn l_Lean_Elab_Frontend_updateCmdPos___redArg(
    mut v_a_1522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserState_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commandState_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commands_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v_pos_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut v_unused_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1524_ = lean_st_ref_take(v_a_1522_);
                v_parserState_1525_ = crate::leanh::lean_ctor_get(v___x_1524_, 1);
                v_commandState_1526_ = crate::leanh::lean_ctor_get(v___x_1524_, 0);
                v_commands_1527_ = crate::leanh::lean_ctor_get(v___x_1524_, 3);
                v_isSharedCheck_1538_ = (!crate::leanh::lean_is_exclusive(v___x_1524_)) as u8;
                if v_isSharedCheck_1538_ == 0 {
                    v_unused_1539_ = crate::leanh::lean_ctor_get(v___x_1524_, 2);
                    crate::leanh::lean_dec(v_unused_1539_);
                    v___x_1529_ = v___x_1524_;
                    v_isShared_1530_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_commands_1527_);
                    crate::leanh::lean_inc(v_parserState_1525_);
                    crate::leanh::lean_inc(v_commandState_1526_);
                    crate::leanh::lean_dec(v___x_1524_);
                    v___x_1529_ = crate::leanh::lean_box(0);
                    v_isShared_1530_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_pos_1531_ = crate::leanh::lean_ctor_get(v_parserState_1525_, 0);
                crate::leanh::lean_inc(v_pos_1531_);
                if v_isShared_1530_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1529_, 2, v_pos_1531_);
                    v___x_1533_ = v___x_1529_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1537_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_commandState_1526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_parserState_1525_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_pos_1531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 3, v_commands_1527_);
                    v___x_1533_ = v_reuseFailAlloc_1537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1534_ = lean_st_ref_set(v_a_1522_, v___x_1533_);
                v___x_1535_ = crate::leanh::lean_box(0);
                v___x_1536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1536_, 0, v___x_1535_);
                return v___x_1536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Frontend_updateCmdPos___redArg___boxed(
    mut v_a_1540_: *mut crate::leanh::LeanObject,
    mut v_a_1541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_1540_);
    crate::leanh::lean_dec(v_a_1540_);
    return v_res_1542_;
}
pub unsafe fn l_Lean_Elab_Frontend_updateCmdPos(
    mut v_a_1543_: *mut crate::leanh::LeanObject,
    mut v_a_1544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_1544_);
    return v___x_1546_;
}
pub unsafe fn l_Lean_Elab_Frontend_updateCmdPos___boxed(
    mut v_a_1547_: *mut crate::leanh::LeanObject,
    mut v_a_1548_: *mut crate::leanh::LeanObject,
    mut v_a_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Lean_Elab_Frontend_updateCmdPos(v_a_1547_, v_a_1548_);
    crate::leanh::lean_dec(v_a_1548_);
    crate::leanh::lean_dec_ref(v_a_1547_);
    return v_res_1550_;
}
pub unsafe fn l_Lean_Elab_Frontend_getParserState___redArg(
    mut v_a_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserState_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1553_ = lean_st_ref_get(v_a_1551_);
    v_parserState_1554_ = crate::leanh::lean_ctor_get(v___x_1553_, 1);
    crate::leanh::lean_inc_ref(v_parserState_1554_);
    crate::leanh::lean_dec(v___x_1553_);
    v___x_1555_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1555_, 0, v_parserState_1554_);
    return v___x_1555_;
}
pub unsafe fn l_Lean_Elab_Frontend_getParserState___redArg___boxed(
    mut v_a_1556_: *mut crate::leanh::LeanObject,
    mut v_a_1557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1558_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_1556_);
    crate::leanh::lean_dec(v_a_1556_);
    return v_res_1558_;
}
pub unsafe fn l_Lean_Elab_Frontend_getParserState(
    mut v_a_1559_: *mut crate::leanh::LeanObject,
    mut v_a_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_1560_);
    return v___x_1562_;
}
pub unsafe fn l_Lean_Elab_Frontend_getParserState___boxed(
    mut v_a_1563_: *mut crate::leanh::LeanObject,
    mut v_a_1564_: *mut crate::leanh::LeanObject,
    mut v_a_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1566_ = l_Lean_Elab_Frontend_getParserState(v_a_1563_, v_a_1564_);
    crate::leanh::lean_dec(v_a_1564_);
    crate::leanh::lean_dec_ref(v_a_1563_);
    return v_res_1566_;
}
pub unsafe fn l_Lean_Elab_Frontend_getCommandState___redArg(
    mut v_a_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commandState_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1569_ = lean_st_ref_get(v_a_1567_);
    v_commandState_1570_ = crate::leanh::lean_ctor_get(v___x_1569_, 0);
    crate::leanh::lean_inc_ref(v_commandState_1570_);
    crate::leanh::lean_dec(v___x_1569_);
    v___x_1571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1571_, 0, v_commandState_1570_);
    return v___x_1571_;
}
pub unsafe fn l_Lean_Elab_Frontend_getCommandState___redArg___boxed(
    mut v_a_1572_: *mut crate::leanh::LeanObject,
    mut v_a_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_1572_);
    crate::leanh::lean_dec(v_a_1572_);
    return v_res_1574_;
}
pub unsafe fn l_Lean_Elab_Frontend_getCommandState(
    mut v_a_1575_: *mut crate::leanh::LeanObject,
    mut v_a_1576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1578_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_1576_);
    return v___x_1578_;
}
pub unsafe fn l_Lean_Elab_Frontend_getCommandState___boxed(
    mut v_a_1579_: *mut crate::leanh::LeanObject,
    mut v_a_1580_: *mut crate::leanh::LeanObject,
    mut v_a_1581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1582_ = l_Lean_Elab_Frontend_getCommandState(v_a_1579_, v_a_1580_);
    crate::leanh::lean_dec(v_a_1580_);
    crate::leanh::lean_dec_ref(v_a_1579_);
    return v_res_1582_;
}
pub unsafe fn l_Lean_Elab_Frontend_setParserState___redArg(
    mut v_ps_1583_: *mut crate::leanh::LeanObject,
    mut v_a_1584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commandState_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commands_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1592_: u8 = 0;
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1599_: u8 = 0;
    let mut v_unused_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1586_ = lean_st_ref_take(v_a_1584_);
                v_commandState_1587_ = crate::leanh::lean_ctor_get(v___x_1586_, 0);
                v_cmdPos_1588_ = crate::leanh::lean_ctor_get(v___x_1586_, 2);
                v_commands_1589_ = crate::leanh::lean_ctor_get(v___x_1586_, 3);
                v_isSharedCheck_1599_ = (!crate::leanh::lean_is_exclusive(v___x_1586_)) as u8;
                if v_isSharedCheck_1599_ == 0 {
                    v_unused_1600_ = crate::leanh::lean_ctor_get(v___x_1586_, 1);
                    crate::leanh::lean_dec(v_unused_1600_);
                    v___x_1591_ = v___x_1586_;
                    v_isShared_1592_ = v_isSharedCheck_1599_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_commands_1589_);
                    crate::leanh::lean_inc(v_cmdPos_1588_);
                    crate::leanh::lean_inc(v_commandState_1587_);
                    crate::leanh::lean_dec(v___x_1586_);
                    v___x_1591_ = crate::leanh::lean_box(0);
                    v_isShared_1592_ = v_isSharedCheck_1599_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1592_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1591_, 1, v_ps_1583_);
                    v___x_1594_ = v___x_1591_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1598_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_commandState_1587_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_ps_1583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1598_, 2, v_cmdPos_1588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1598_, 3, v_commands_1589_);
                    v___x_1594_ = v_reuseFailAlloc_1598_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1595_ = lean_st_ref_set(v_a_1584_, v___x_1594_);
                v___x_1596_ = crate::leanh::lean_box(0);
                v___x_1597_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1597_, 0, v___x_1596_);
                return v___x_1597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Frontend_setParserState___redArg___boxed(
    mut v_ps_1601_: *mut crate::leanh::LeanObject,
    mut v_a_1602_: *mut crate::leanh::LeanObject,
    mut v_a_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1604_ = l_Lean_Elab_Frontend_setParserState___redArg(v_ps_1601_, v_a_1602_);
    crate::leanh::lean_dec(v_a_1602_);
    return v_res_1604_;
}
pub unsafe fn l_Lean_Elab_Frontend_setParserState(
    mut v_ps_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1609_ = l_Lean_Elab_Frontend_setParserState___redArg(v_ps_1605_, v_a_1607_);
    return v___x_1609_;
}
pub unsafe fn l_Lean_Elab_Frontend_setParserState___boxed(
    mut v_ps_1610_: *mut crate::leanh::LeanObject,
    mut v_a_1611_: *mut crate::leanh::LeanObject,
    mut v_a_1612_: *mut crate::leanh::LeanObject,
    mut v_a_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1614_ = l_Lean_Elab_Frontend_setParserState(v_ps_1610_, v_a_1611_, v_a_1612_);
    crate::leanh::lean_dec(v_a_1612_);
    crate::leanh::lean_dec_ref(v_a_1611_);
    return v_res_1614_;
}
pub unsafe fn l_Lean_Elab_Frontend_setMessages___redArg(
    mut v_msgs_1615_: *mut crate::leanh::LeanObject,
    mut v_a_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commandState_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserState_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commands_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v_env_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1638_: u8 = 0;
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1648_: u8 = 0;
    let mut v_unused_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1650_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1618_ = lean_st_ref_take(v_a_1616_);
                v_commandState_1619_ = crate::leanh::lean_ctor_get(v___x_1618_, 0);
                v_parserState_1620_ = crate::leanh::lean_ctor_get(v___x_1618_, 1);
                v_cmdPos_1621_ = crate::leanh::lean_ctor_get(v___x_1618_, 2);
                v_commands_1622_ = crate::leanh::lean_ctor_get(v___x_1618_, 3);
                v_isSharedCheck_1650_ = (!crate::leanh::lean_is_exclusive(v___x_1618_)) as u8;
                if v_isSharedCheck_1650_ == 0 {
                    v___x_1624_ = v___x_1618_;
                    v_isShared_1625_ = v_isSharedCheck_1650_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_commands_1622_);
                    crate::leanh::lean_inc(v_cmdPos_1621_);
                    crate::leanh::lean_inc(v_parserState_1620_);
                    crate::leanh::lean_inc(v_commandState_1619_);
                    crate::leanh::lean_dec(v___x_1618_);
                    v___x_1624_ = crate::leanh::lean_box(0);
                    v_isShared_1625_ = v_isSharedCheck_1650_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_env_1626_ = crate::leanh::lean_ctor_get(v_commandState_1619_, 0);
                v_scopes_1627_ = crate::leanh::lean_ctor_get(v_commandState_1619_, 2);
                v_usedQuotCtxts_1628_ = crate::leanh::lean_ctor_get(v_commandState_1619_, 3);
                v_nextMacroScope_1629_ = crate::leanh::lean_ctor_get(v_commandState_1619_, 4);
                v_maxRecDepth_1630_ = crate::leanh::lean_ctor_get(v_commandState_1619_, 5);
                v_ngen_1631_ = crate::leanh::lean_ctor_get(v_commandState_1619_, 6);
                v_auxDeclNGen_1632_ = crate::leanh::lean_ctor_get(v_commandState_1619_, 7);
                v_infoState_1633_ = crate::leanh::lean_ctor_get(v_commandState_1619_, 8);
                v_traceState_1634_ = crate::leanh::lean_ctor_get(v_commandState_1619_, 9);
                v_snapshotTasks_1635_ = crate::leanh::lean_ctor_get(v_commandState_1619_, 10);
                v_isSharedCheck_1648_ =
                    (!crate::leanh::lean_is_exclusive(v_commandState_1619_)) as u8;
                if v_isSharedCheck_1648_ == 0 {
                    v_unused_1649_ = crate::leanh::lean_ctor_get(v_commandState_1619_, 1);
                    crate::leanh::lean_dec(v_unused_1649_);
                    v___x_1637_ = v_commandState_1619_;
                    v_isShared_1638_ = v_isSharedCheck_1648_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1635_);
                    crate::leanh::lean_inc(v_traceState_1634_);
                    crate::leanh::lean_inc(v_infoState_1633_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1632_);
                    crate::leanh::lean_inc(v_ngen_1631_);
                    crate::leanh::lean_inc(v_maxRecDepth_1630_);
                    crate::leanh::lean_inc(v_nextMacroScope_1629_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_1628_);
                    crate::leanh::lean_inc(v_scopes_1627_);
                    crate::leanh::lean_inc(v_env_1626_);
                    crate::leanh::lean_dec(v_commandState_1619_);
                    v___x_1637_ = crate::leanh::lean_box(0);
                    v_isShared_1638_ = v_isSharedCheck_1648_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1637_, 1, v_msgs_1615_);
                    v___x_1640_ = v___x_1637_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1647_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_env_1626_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_msgs_1615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_scopes_1627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_usedQuotCtxts_1628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_nextMacroScope_1629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 5, v_maxRecDepth_1630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 6, v_ngen_1631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 7, v_auxDeclNGen_1632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 8, v_infoState_1633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 9, v_traceState_1634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 10, v_snapshotTasks_1635_);
                    v___x_1640_ = v_reuseFailAlloc_1647_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1624_, 0, v___x_1640_);
                    v___x_1642_ = v___x_1624_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1646_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_parserState_1620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_cmdPos_1621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 3, v_commands_1622_);
                    v___x_1642_ = v_reuseFailAlloc_1646_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1643_ = lean_st_ref_set(v_a_1616_, v___x_1642_);
                v___x_1644_ = crate::leanh::lean_box(0);
                v___x_1645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1645_, 0, v___x_1644_);
                return v___x_1645_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Frontend_setMessages___redArg___boxed(
    mut v_msgs_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1654_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_1651_, v_a_1652_);
    crate::leanh::lean_dec(v_a_1652_);
    return v_res_1654_;
}
pub unsafe fn l_Lean_Elab_Frontend_setMessages(
    mut v_msgs_1655_: *mut crate::leanh::LeanObject,
    mut v_a_1656_: *mut crate::leanh::LeanObject,
    mut v_a_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_1655_, v_a_1657_);
    return v___x_1659_;
}
pub unsafe fn l_Lean_Elab_Frontend_setMessages___boxed(
    mut v_msgs_1660_: *mut crate::leanh::LeanObject,
    mut v_a_1661_: *mut crate::leanh::LeanObject,
    mut v_a_1662_: *mut crate::leanh::LeanObject,
    mut v_a_1663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1664_ = l_Lean_Elab_Frontend_setMessages(v_msgs_1660_, v_a_1661_, v_a_1662_);
    crate::leanh::lean_dec(v_a_1662_);
    crate::leanh::lean_dec_ref(v_a_1661_);
    return v_res_1664_;
}
pub unsafe fn l_Lean_Elab_Frontend_getInputContext___redArg(
    mut v_a_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_1665_);
    v___x_1667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1667_, 0, v_a_1665_);
    return v___x_1667_;
}
pub unsafe fn l_Lean_Elab_Frontend_getInputContext___redArg___boxed(
    mut v_a_1668_: *mut crate::leanh::LeanObject,
    mut v_a_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1670_ = l_Lean_Elab_Frontend_getInputContext___redArg(v_a_1668_);
    crate::leanh::lean_dec_ref(v_a_1668_);
    return v_res_1670_;
}
pub unsafe fn l_Lean_Elab_Frontend_getInputContext(
    mut v_a_1671_: *mut crate::leanh::LeanObject,
    mut v_a_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_1671_);
    v___x_1674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1674_, 0, v_a_1671_);
    return v___x_1674_;
}
pub unsafe fn l_Lean_Elab_Frontend_getInputContext___boxed(
    mut v_a_1675_: *mut crate::leanh::LeanObject,
    mut v_a_1676_: *mut crate::leanh::LeanObject,
    mut v_a_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1678_ = l_Lean_Elab_Frontend_getInputContext(v_a_1675_, v_a_1676_);
    crate::leanh::lean_dec(v_a_1676_);
    crate::leanh::lean_dec_ref(v_a_1675_);
    return v_res_1678_;
}
pub unsafe fn l_Lean_Elab_Frontend_processCommand___lam__0(
    mut v_a_1679_: *mut crate::leanh::LeanObject,
    mut v___x_1680_: *mut crate::leanh::LeanObject,
    mut v_a_1681_: *mut crate::leanh::LeanObject,
    mut v_messages_1682_: *mut crate::leanh::LeanObject,
    mut v_x_1683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_1679_);
    v___x_1684_ = l_Lean_Parser_parseCommand(v_a_1679_, v___x_1680_, v_a_1681_, v_messages_1682_);
    return v___x_1684_;
}
pub unsafe fn l_Lean_Elab_Frontend_processCommand___lam__0___boxed(
    mut v_a_1685_: *mut crate::leanh::LeanObject,
    mut v___x_1686_: *mut crate::leanh::LeanObject,
    mut v_a_1687_: *mut crate::leanh::LeanObject,
    mut v_messages_1688_: *mut crate::leanh::LeanObject,
    mut v_x_1689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1690_ = l_Lean_Elab_Frontend_processCommand___lam__0(
        v_a_1685_,
        v___x_1686_,
        v_a_1687_,
        v_messages_1688_,
        v_x_1689_,
    );
    crate::leanh::lean_dec_ref(v_a_1685_);
    return v_res_1690_;
}
pub unsafe fn l_Lean_Elab_Frontend_processCommand(
    mut v_a_1692_: *mut crate::leanh::LeanObject,
    mut v_a_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commandState_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserState_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commands_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1724_: u8 = 0;
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1734_: u8 = 0;
    let mut v___x_1735_: u8 = 0;
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1740_: u8 = 0;
    let mut v_unused_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1745_: u8 = 0;
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1749_: u8 = 0;
    let mut v_reuseFailAlloc_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1695_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_1693_);
                crate::leanh::lean_dec_ref(v___x_1695_);
                v___x_1696_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_1693_);
                v_a_1697_ = crate::leanh::lean_ctor_get(v___x_1696_, 0);
                crate::leanh::lean_inc(v_a_1697_);
                crate::leanh::lean_dec_ref(v___x_1696_);
                v___x_1698_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_1693_);
                v_a_1699_ = crate::leanh::lean_ctor_get(v___x_1698_, 0);
                crate::leanh::lean_inc(v_a_1699_);
                crate::leanh::lean_dec_ref(v___x_1698_);
                v_env_1700_ = crate::leanh::lean_ctor_get(v_a_1697_, 0);
                crate::leanh::lean_inc_ref(v_env_1700_);
                v_messages_1701_ = crate::leanh::lean_ctor_get(v_a_1697_, 1);
                crate::leanh::lean_inc_ref(v_messages_1701_);
                v_scopes_1702_ = crate::leanh::lean_ctor_get(v_a_1697_, 2);
                crate::leanh::lean_inc(v_scopes_1702_);
                crate::leanh::lean_dec(v_a_1697_);
                v___x_1703_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_1704_ = l_List_head_x21___redArg(v___x_1703_, v_scopes_1702_);
                crate::leanh::lean_dec(v_scopes_1702_);
                v_opts_1705_ = crate::leanh::lean_ctor_get(v___x_1704_, 1);
                crate::leanh::lean_inc_ref_n(v_opts_1705_, 2);
                v_currNamespace_1706_ = crate::leanh::lean_ctor_get(v___x_1704_, 2);
                crate::leanh::lean_inc(v_currNamespace_1706_);
                v_openDecls_1707_ = crate::leanh::lean_ctor_get(v___x_1704_, 3);
                crate::leanh::lean_inc(v_openDecls_1707_);
                crate::leanh::lean_dec(v___x_1704_);
                v___x_1708_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1708_, 0, v_env_1700_);
                crate::leanh::lean_ctor_set(v___x_1708_, 1, v_opts_1705_);
                crate::leanh::lean_ctor_set(v___x_1708_, 2, v_currNamespace_1706_);
                crate::leanh::lean_ctor_set(v___x_1708_, 3, v_openDecls_1707_);
                crate::leanh::lean_inc_ref(v_a_1692_);
                v___f_1709_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Frontend_processCommand___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_1709_, 0, v_a_1692_);
                crate::leanh::lean_closure_set(v___f_1709_, 1, v___x_1708_);
                crate::leanh::lean_closure_set(v___f_1709_, 2, v_a_1699_);
                crate::leanh::lean_closure_set(v___f_1709_, 3, v_messages_1701_);
                v___x_1710_ = l_Lean_Elab_Frontend_processCommand___closed__0;
                v___x_1711_ = crate::leanh::lean_box(0);
                v___x_1712_ = lean_profileit(v___x_1710_, v_opts_1705_, v___f_1709_, v___x_1711_);
                crate::leanh::lean_dec_ref(v_opts_1705_);
                v_snd_1713_ = crate::leanh::lean_ctor_get(v___x_1712_, 1);
                crate::leanh::lean_inc(v_snd_1713_);
                v_fst_1714_ = crate::leanh::lean_ctor_get(v___x_1712_, 0);
                crate::leanh::lean_inc(v_fst_1714_);
                crate::leanh::lean_dec(v___x_1712_);
                v_fst_1715_ = crate::leanh::lean_ctor_get(v_snd_1713_, 0);
                crate::leanh::lean_inc(v_fst_1715_);
                v_snd_1716_ = crate::leanh::lean_ctor_get(v_snd_1713_, 1);
                crate::leanh::lean_inc(v_snd_1716_);
                crate::leanh::lean_dec(v_snd_1713_);
                v___x_1717_ = lean_st_ref_take(v_a_1693_);
                v_commandState_1718_ = crate::leanh::lean_ctor_get(v___x_1717_, 0);
                v_parserState_1719_ = crate::leanh::lean_ctor_get(v___x_1717_, 1);
                v_cmdPos_1720_ = crate::leanh::lean_ctor_get(v___x_1717_, 2);
                v_commands_1721_ = crate::leanh::lean_ctor_get(v___x_1717_, 3);
                v_isSharedCheck_1751_ = (!crate::leanh::lean_is_exclusive(v___x_1717_)) as u8;
                if v_isSharedCheck_1751_ == 0 {
                    v___x_1723_ = v___x_1717_;
                    v_isShared_1724_ = v_isSharedCheck_1751_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_commands_1721_);
                    crate::leanh::lean_inc(v_cmdPos_1720_);
                    crate::leanh::lean_inc(v_parserState_1719_);
                    crate::leanh::lean_inc(v_commandState_1718_);
                    crate::leanh::lean_dec(v___x_1717_);
                    v___x_1723_ = crate::leanh::lean_box(0);
                    v_isShared_1724_ = v_isSharedCheck_1751_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_fst_1714_);
                v___x_1725_ = lean_array_push(v_commands_1721_, v_fst_1714_);
                if v_isShared_1724_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1723_, 3, v___x_1725_);
                    v___x_1727_ = v___x_1723_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_commandState_1718_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_parserState_1719_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 2, v_cmdPos_1720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 3, v___x_1725_);
                    v___x_1727_ = v_reuseFailAlloc_1750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1728_ = lean_st_ref_set(v_a_1693_, v___x_1727_);
                v___x_1729_ = l_Lean_Elab_Frontend_setParserState___redArg(v_fst_1715_, v_a_1693_);
                crate::leanh::lean_dec_ref(v___x_1729_);
                v___x_1730_ = l_Lean_Elab_Frontend_setMessages___redArg(v_snd_1716_, v_a_1693_);
                crate::leanh::lean_dec_ref(v___x_1730_);
                crate::leanh::lean_inc(v_fst_1714_);
                v___x_1731_ =
                    l_Lean_Elab_Frontend_elabCommandAtFrontend(v_fst_1714_, v_a_1692_, v_a_1693_);
                if crate::leanh::lean_obj_tag(v___x_1731_) == 0 {
                    v_isSharedCheck_1740_ = (!crate::leanh::lean_is_exclusive(v___x_1731_)) as u8;
                    if v_isSharedCheck_1740_ == 0 {
                        v_unused_1741_ = crate::leanh::lean_ctor_get(v___x_1731_, 0);
                        crate::leanh::lean_dec(v_unused_1741_);
                        v___x_1733_ = v___x_1731_;
                        v_isShared_1734_ = v_isSharedCheck_1740_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1731_);
                        v___x_1733_ = crate::leanh::lean_box(0);
                        v_isShared_1734_ = v_isSharedCheck_1740_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_1714_);
                    v_a_1742_ = crate::leanh::lean_ctor_get(v___x_1731_, 0);
                    v_isSharedCheck_1749_ = (!crate::leanh::lean_is_exclusive(v___x_1731_)) as u8;
                    if v_isSharedCheck_1749_ == 0 {
                        v___x_1744_ = v___x_1731_;
                        v_isShared_1745_ = v_isSharedCheck_1749_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1742_);
                        crate::leanh::lean_dec(v___x_1731_);
                        v___x_1744_ = crate::leanh::lean_box(0);
                        v_isShared_1745_ = v_isSharedCheck_1749_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1735_ = l_Lean_Parser_isTerminalCommand(v_fst_1714_);
                v___x_1736_ = crate::leanh::lean_box((v___x_1735_) as usize);
                if v_isShared_1734_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1733_, 0, v___x_1736_);
                    v___x_1738_ = v___x_1733_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1739_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
                    v___x_1738_ = v_reuseFailAlloc_1739_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1738_;
            }
            5 => {
                if v_isShared_1745_ == 0 {
                    v___x_1747_ = v___x_1744_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1748_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
                    v___x_1747_ = v_reuseFailAlloc_1748_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1747_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Frontend_processCommand___boxed(
    mut v_a_1752_: *mut crate::leanh::LeanObject,
    mut v_a_1753_: *mut crate::leanh::LeanObject,
    mut v_a_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1755_ = l_Lean_Elab_Frontend_processCommand(v_a_1752_, v_a_1753_);
    crate::leanh::lean_dec(v_a_1753_);
    crate::leanh::lean_dec_ref(v_a_1752_);
    return v_res_1755_;
}
pub unsafe fn l_Lean_Elab_Frontend_processCommands(
    mut v_a_1756_: *mut crate::leanh::LeanObject,
    mut v_a_1757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut v_a_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1774_: u8 = 0;
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1759_ = l_Lean_Elab_Frontend_processCommand(v_a_1756_, v_a_1757_);
                if crate::leanh::lean_obj_tag(v___x_1759_) == 0 {
                    v_a_1760_ = crate::leanh::lean_ctor_get(v___x_1759_, 0);
                    v_isSharedCheck_1770_ = (!crate::leanh::lean_is_exclusive(v___x_1759_)) as u8;
                    if v_isSharedCheck_1770_ == 0 {
                        v___x_1762_ = v___x_1759_;
                        v_isShared_1763_ = v_isSharedCheck_1770_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1760_);
                        crate::leanh::lean_dec(v___x_1759_);
                        v___x_1762_ = crate::leanh::lean_box(0);
                        v_isShared_1763_ = v_isSharedCheck_1770_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1771_ = crate::leanh::lean_ctor_get(v___x_1759_, 0);
                    v_isSharedCheck_1778_ = (!crate::leanh::lean_is_exclusive(v___x_1759_)) as u8;
                    if v_isSharedCheck_1778_ == 0 {
                        v___x_1773_ = v___x_1759_;
                        v_isShared_1774_ = v_isSharedCheck_1778_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1771_);
                        crate::leanh::lean_dec(v___x_1759_);
                        v___x_1773_ = crate::leanh::lean_box(0);
                        v_isShared_1774_ = v_isSharedCheck_1778_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1764_ = (crate::leanh::lean_unbox(v_a_1760_) as u8);
                crate::leanh::lean_dec(v_a_1760_);
                if v___x_1764_ == 0 {
                    crate::leanh::lean_del_object(v___x_1762_);
                    state = 0;
                    continue;
                } else {
                    v___x_1766_ = crate::leanh::lean_box(0);
                    if v_isShared_1763_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1762_, 0, v___x_1766_);
                        v___x_1768_ = v___x_1762_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1769_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
                        v___x_1768_ = v_reuseFailAlloc_1769_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1768_;
            }
            3 => {
                if v_isShared_1774_ == 0 {
                    v___x_1776_ = v___x_1773_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1777_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
                    v___x_1776_ = v_reuseFailAlloc_1777_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1776_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Frontend_processCommands___boxed(
    mut v_a_1779_: *mut crate::leanh::LeanObject,
    mut v_a_1780_: *mut crate::leanh::LeanObject,
    mut v_a_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1782_ = l_Lean_Elab_Frontend_processCommands(v_a_1779_, v_a_1780_);
    crate::leanh::lean_dec(v_a_1780_);
    crate::leanh::lean_dec_ref(v_a_1779_);
    return v_res_1782_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(
    mut v_as_1783_: *mut crate::leanh::LeanObject,
    mut v_i_1784_: usize,
    mut v_stop_1785_: usize,
    mut v_b_1786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: usize = 0;
    let mut v___x_1790_: usize = 0;
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1792_ = lean_usize_dec_eq(v_i_1784_, v_stop_1785_);
                if v___x_1792_ == 0 {
                    v___x_1793_ = lean_array_uget_borrowed(v_as_1783_, v_i_1784_);
                    if crate::leanh::lean_obj_tag(v___x_1793_) == 0 {
                        v___y_1788_ = v_b_1786_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1794_ = crate::leanh::lean_ctor_get(v___x_1793_, 0);
                        crate::leanh::lean_inc(v_val_1794_);
                        v___x_1795_ = lean_array_push(v_b_1786_, v_val_1794_);
                        v___y_1788_ = v___x_1795_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1786_;
                }
            }
            1 => {
                v___x_1789_ = 1usize;
                v___x_1790_ = lean_usize_add(v_i_1784_, v___x_1789_);
                v_i_1784_ = v___x_1790_;
                v_b_1786_ = v___y_1788_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(
    mut v_as_1796_: *mut crate::leanh::LeanObject,
    mut v_i_1797_: *mut crate::leanh::LeanObject,
    mut v_stop_1798_: *mut crate::leanh::LeanObject,
    mut v_b_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1800_: usize = 0;
    let mut v_stop_boxed_1801_: usize = 0;
    let mut v_res_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1800_ = crate::leanh::lean_unbox_usize(v_i_1797_);
    crate::leanh::lean_dec(v_i_1797_);
    v_stop_boxed_1801_ = crate::leanh::lean_unbox_usize(v_stop_1798_);
    crate::leanh::lean_dec(v_stop_1798_);
    v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_1796_, v_i_boxed_1800_, v_stop_boxed_1801_, v_b_1799_);
    crate::leanh::lean_dec_ref(v_as_1796_);
    return v_res_1802_;
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(
    mut v_as_1805_: *mut crate::leanh::LeanObject,
    mut v_start_1806_: *mut crate::leanh::LeanObject,
    mut v_stop_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: u8 = 0;
    v___x_1808_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0;
    v___x_1809_ = lean_nat_dec_lt(v_start_1806_, v_stop_1807_);
    if v___x_1809_ == 0 {
        return v___x_1808_;
    } else {
        let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1811_: u8 = 0;
        v___x_1810_ = lean_array_get_size(v_as_1805_);
        v___x_1811_ = lean_nat_dec_le(v_stop_1807_, v___x_1810_);
        if v___x_1811_ == 0 {
            let mut v___x_1812_: u8 = 0;
            v___x_1812_ = lean_nat_dec_lt(v_start_1806_, v___x_1810_);
            if v___x_1812_ == 0 {
                return v___x_1808_;
            } else {
                let mut v___x_1813_: usize = 0;
                let mut v___x_1814_: usize = 0;
                let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1813_ = lean_usize_of_nat(v_start_1806_);
                v___x_1814_ = lean_usize_of_nat(v___x_1810_);
                v___x_1815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_1805_, v___x_1813_, v___x_1814_, v___x_1808_);
                return v___x_1815_;
            }
        } else {
            let mut v___x_1816_: usize = 0;
            let mut v___x_1817_: usize = 0;
            let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1816_ = lean_usize_of_nat(v_start_1806_);
            v___x_1817_ = lean_usize_of_nat(v_stop_1807_);
            v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_1805_, v___x_1816_, v___x_1817_, v___x_1808_);
            return v___x_1818_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(
    mut v_as_1819_: *mut crate::leanh::LeanObject,
    mut v_start_1820_: *mut crate::leanh::LeanObject,
    mut v_stop_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1822_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v_as_1819_, v_start_1820_, v_stop_1821_);
    crate::leanh::lean_dec(v_stop_1821_);
    crate::leanh::lean_dec(v_start_1820_);
    crate::leanh::lean_dec_ref(v_as_1819_);
    return v_res_1822_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(
    mut v_sz_1823_: usize,
    mut v_i_1824_: usize,
    mut v_bs_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1826_: u8 = 0;
    let mut v_v_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elabSnap_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoTreeSnap_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoTree_x3f_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: usize = 0;
    let mut v___x_1835_: usize = 0;
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1826_ = lean_usize_dec_lt(v_i_1824_, v_sz_1823_);
                if v___x_1826_ == 0 {
                    return v_bs_1825_;
                } else {
                    v_v_1827_ = lean_array_uget_borrowed(v_bs_1825_, v_i_1824_);
                    v_elabSnap_1828_ = crate::leanh::lean_ctor_get(v_v_1827_, 3);
                    v_infoTreeSnap_1829_ = crate::leanh::lean_ctor_get(v_elabSnap_1828_, 3);
                    crate::leanh::lean_inc_ref(v_infoTreeSnap_1829_);
                    v___x_1830_ = l_Lean_Language_SnapshotTask_get___redArg(v_infoTreeSnap_1829_);
                    v_infoTree_x3f_1831_ = crate::leanh::lean_ctor_get(v___x_1830_, 2);
                    crate::leanh::lean_inc(v_infoTree_x3f_1831_);
                    crate::leanh::lean_dec(v___x_1830_);
                    v___x_1832_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1833_ = lean_array_uset(v_bs_1825_, v_i_1824_, v___x_1832_);
                    v___x_1834_ = 1usize;
                    v___x_1835_ = lean_usize_add(v_i_1824_, v___x_1834_);
                    v___x_1836_ = lean_array_uset(v_bs_x27_1833_, v_i_1824_, v_infoTree_x3f_1831_);
                    v_i_1824_ = v___x_1835_;
                    v_bs_1825_ = v___x_1836_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(
    mut v_sz_1838_: *mut crate::leanh::LeanObject,
    mut v_i_1839_: *mut crate::leanh::LeanObject,
    mut v_bs_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1841_: usize = 0;
    let mut v_i_boxed_1842_: usize = 0;
    let mut v_res_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1841_ = crate::leanh::lean_unbox_usize(v_sz_1838_);
    crate::leanh::lean_dec(v_sz_1838_);
    v_i_boxed_1842_ = crate::leanh::lean_unbox_usize(v_i_1839_);
    crate::leanh::lean_dec(v_i_1839_);
    v_res_1843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_boxed_1841_, v_i_boxed_1842_, v_bs_1840_);
    return v_res_1843_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(
    mut v_as_1844_: *mut crate::leanh::LeanObject,
    mut v_i_1845_: usize,
    mut v_stop_1846_: usize,
    mut v_b_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: usize = 0;
    let mut v___x_1852_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1848_ = lean_usize_dec_eq(v_i_1845_, v_stop_1846_);
                if v___x_1848_ == 0 {
                    v___x_1849_ = lean_array_uget_borrowed(v_as_1844_, v_i_1845_);
                    crate::leanh::lean_inc(v___x_1849_);
                    v___x_1850_ = l_Lean_MessageLog_append(v_b_1847_, v___x_1849_);
                    v___x_1851_ = 1usize;
                    v___x_1852_ = lean_usize_add(v_i_1845_, v___x_1851_);
                    v_i_1845_ = v___x_1852_;
                    v_b_1847_ = v___x_1850_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1847_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(
    mut v_as_1854_: *mut crate::leanh::LeanObject,
    mut v_i_1855_: *mut crate::leanh::LeanObject,
    mut v_stop_1856_: *mut crate::leanh::LeanObject,
    mut v_b_1857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1858_: usize = 0;
    let mut v_stop_boxed_1859_: usize = 0;
    let mut v_res_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1858_ = crate::leanh::lean_unbox_usize(v_i_1855_);
    crate::leanh::lean_dec(v_i_1855_);
    v_stop_boxed_1859_ = crate::leanh::lean_unbox_usize(v_stop_1856_);
    crate::leanh::lean_dec(v_stop_1856_);
    v_res_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_as_1854_, v_i_boxed_1858_, v_stop_boxed_1859_, v_b_1857_);
    crate::leanh::lean_dec_ref(v_as_1854_);
    return v_res_1860_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(
    mut v_sz_1861_: usize,
    mut v_i_1862_: usize,
    mut v_bs_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1864_: u8 = 0;
    let mut v_v_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: usize = 0;
    let mut v___x_1870_: usize = 0;
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1864_ = lean_usize_dec_lt(v_i_1862_, v_sz_1861_);
                if v___x_1864_ == 0 {
                    return v_bs_1863_;
                } else {
                    v_v_1865_ = lean_array_uget_borrowed(v_bs_1863_, v_i_1862_);
                    v_stx_1866_ = crate::leanh::lean_ctor_get(v_v_1865_, 1);
                    crate::leanh::lean_inc(v_stx_1866_);
                    v___x_1867_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1868_ = lean_array_uset(v_bs_1863_, v_i_1862_, v___x_1867_);
                    v___x_1869_ = 1usize;
                    v___x_1870_ = lean_usize_add(v_i_1862_, v___x_1869_);
                    v___x_1871_ = lean_array_uset(v_bs_x27_1868_, v_i_1862_, v_stx_1866_);
                    v_i_1862_ = v___x_1870_;
                    v_bs_1863_ = v___x_1871_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(
    mut v_sz_1873_: *mut crate::leanh::LeanObject,
    mut v_i_1874_: *mut crate::leanh::LeanObject,
    mut v_bs_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1876_: usize = 0;
    let mut v_i_boxed_1877_: usize = 0;
    let mut v_res_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1876_ = crate::leanh::lean_unbox_usize(v_sz_1873_);
    crate::leanh::lean_dec(v_sz_1873_);
    v_i_boxed_1877_ = crate::leanh::lean_unbox_usize(v_i_1874_);
    crate::leanh::lean_dec(v_i_1874_);
    v_res_1878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_boxed_1876_, v_i_boxed_1877_, v_bs_1875_);
    return v_res_1878_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(
    mut v_sz_1879_: usize,
    mut v_i_1880_: usize,
    mut v_bs_1881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1882_: u8 = 0;
    let mut v_v_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgLog_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: usize = 0;
    let mut v___x_1889_: usize = 0;
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1882_ = lean_usize_dec_lt(v_i_1880_, v_sz_1879_);
                if v___x_1882_ == 0 {
                    return v_bs_1881_;
                } else {
                    v_v_1883_ = lean_array_uget_borrowed(v_bs_1881_, v_i_1880_);
                    v_diagnostics_1884_ = crate::leanh::lean_ctor_get(v_v_1883_, 1);
                    v_msgLog_1885_ = crate::leanh::lean_ctor_get(v_diagnostics_1884_, 0);
                    crate::leanh::lean_inc_ref(v_msgLog_1885_);
                    v___x_1886_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1887_ = lean_array_uset(v_bs_1881_, v_i_1880_, v___x_1886_);
                    v___x_1888_ = 1usize;
                    v___x_1889_ = lean_usize_add(v_i_1880_, v___x_1888_);
                    v___x_1890_ = lean_array_uset(v_bs_x27_1887_, v_i_1880_, v_msgLog_1885_);
                    v_i_1880_ = v___x_1889_;
                    v_bs_1881_ = v___x_1890_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3___boxed(
    mut v_sz_1892_: *mut crate::leanh::LeanObject,
    mut v_i_1893_: *mut crate::leanh::LeanObject,
    mut v_bs_1894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1895_: usize = 0;
    let mut v_i_boxed_1896_: usize = 0;
    let mut v_res_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1895_ = crate::leanh::lean_unbox_usize(v_sz_1892_);
    crate::leanh::lean_dec(v_sz_1892_);
    v_i_boxed_1896_ = crate::leanh::lean_unbox_usize(v_i_1893_);
    crate::leanh::lean_dec(v_i_1893_);
    v_res_1897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_sz_boxed_1895_, v_i_boxed_1896_, v_bs_1894_);
    return v_res_1897_;
}
pub unsafe fn _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1899_ = lean_mk_empty_array_with_capacity(v___x_1898_);
    v___x_1900_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1900_, 0, v___x_1899_);
    return v___x_1900_;
}
pub unsafe fn _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1901_: usize = 0;
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1901_ = 5usize;
    v___x_1902_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1903_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1904_ = lean_mk_empty_array_with_capacity(v___x_1903_);
    v___x_1905_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0_once), _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0);
    v___x_1906_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1906_, 0, v___x_1905_);
    crate::leanh::lean_ctor_set(v___x_1906_, 1, v___x_1904_);
    crate::leanh::lean_ctor_set(v___x_1906_, 2, v___x_1902_);
    crate::leanh::lean_ctor_set(v___x_1906_, 3, v___x_1902_);
    crate::leanh::lean_ctor_set_usize(v___x_1906_, 4, v___x_1901_);
    return v___x_1906_;
}
pub unsafe fn _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_Lean_NameSet_empty;
    v___x_1908_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1_once), _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1);
    v___x_1909_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1909_, 0, v___x_1908_);
    crate::leanh::lean_ctor_set(v___x_1909_, 1, v___x_1908_);
    crate::leanh::lean_ctor_set(v___x_1909_, 2, v___x_1907_);
    return v___x_1909_;
}
pub unsafe fn l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(
    mut v_inputCtx_1910_: *mut crate::leanh::LeanObject,
    mut v_initialSnap_1911_: *mut crate::leanh::LeanObject,
    mut v_t_1912_: *mut crate::leanh::LeanObject,
    mut v_commands_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snap_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserState_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elabSnap_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCmdSnap_x3f_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commands_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1926_: usize = 0;
    let mut v_resultSnap_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdState_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1942_: u8 = 0;
    let mut v_enabled_1943_: u8 = 0;
    let mut v_assignment_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v_pos_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: usize = 0;
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1964_: u8 = 0;
    let mut v_unused_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1966_: u8 = 0;
    let mut v_unused_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1971_: usize = 0;
    let mut v___x_1972_: usize = 0;
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: u8 = 0;
    let mut v___x_1976_: u8 = 0;
    let mut v___x_1977_: usize = 0;
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: usize = 0;
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snap_1915_ = lean_task_get_own(v_t_1912_);
                v_parserState_1916_ = crate::leanh::lean_ctor_get(v_snap_1915_, 2);
                crate::leanh::lean_inc_ref(v_parserState_1916_);
                v_elabSnap_1917_ = crate::leanh::lean_ctor_get(v_snap_1915_, 3);
                crate::leanh::lean_inc_ref(v_elabSnap_1917_);
                v_nextCmdSnap_x3f_1918_ = crate::leanh::lean_ctor_get(v_snap_1915_, 4);
                crate::leanh::lean_inc(v_nextCmdSnap_x3f_1918_);
                v_commands_1919_ = lean_array_push(v_commands_1913_, v_snap_1915_);
                if crate::leanh::lean_obj_tag(v_nextCmdSnap_x3f_1918_) == 1 {
                    crate::leanh::lean_dec_ref(v_elabSnap_1917_);
                    crate::leanh::lean_dec_ref(v_parserState_1916_);
                    v_val_1920_ = crate::leanh::lean_ctor_get(v_nextCmdSnap_x3f_1918_, 0);
                    crate::leanh::lean_inc(v_val_1920_);
                    crate::leanh::lean_dec_ref_known(v_nextCmdSnap_x3f_1918_, 1);
                    v_task_1921_ = crate::leanh::lean_ctor_get(v_val_1920_, 3);
                    crate::leanh::lean_inc_ref(v_task_1921_);
                    crate::leanh::lean_dec(v_val_1920_);
                    v_t_1912_ = v_task_1921_;
                    v_commands_1913_ = v_commands_1919_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_nextCmdSnap_x3f_1918_);
                    v___x_1923_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1968_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once), _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
                    crate::leanh::lean_inc_ref(v_initialSnap_1911_);
                    v___x_1969_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(
                        v_initialSnap_1911_,
                    );
                    v___x_1970_ = l_Lean_Language_SnapshotTree_getAll(v___x_1969_);
                    v_sz_1971_ = lean_array_size(v___x_1970_);
                    v___x_1972_ = 0usize;
                    v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_sz_1971_, v___x_1972_, v___x_1970_);
                    v___x_1974_ = lean_array_get_size(v___x_1973_);
                    v___x_1975_ = lean_nat_dec_lt(v___x_1923_, v___x_1974_);
                    if v___x_1975_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1973_);
                        v___y_1925_ = v___x_1968_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1976_ = lean_nat_dec_le(v___x_1974_, v___x_1974_);
                        if v___x_1976_ == 0 {
                            if v___x_1975_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_1973_);
                                v___y_1925_ = v___x_1968_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1977_ = lean_usize_of_nat(v___x_1974_);
                                v___x_1978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v___x_1973_, v___x_1972_, v___x_1977_, v___x_1968_);
                                crate::leanh::lean_dec_ref(v___x_1973_);
                                v___y_1925_ = v___x_1978_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1979_ = lean_usize_of_nat(v___x_1974_);
                            v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v___x_1973_, v___x_1972_, v___x_1979_, v___x_1968_);
                            crate::leanh::lean_dec_ref(v___x_1973_);
                            v___y_1925_ = v___x_1980_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_sz_1926_ = lean_array_size(v_commands_1919_);
                v_resultSnap_1927_ = crate::leanh::lean_ctor_get(v_elabSnap_1917_, 2);
                crate::leanh::lean_inc_ref(v_resultSnap_1927_);
                crate::leanh::lean_dec_ref(v_elabSnap_1917_);
                v___x_1928_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_1927_);
                v_cmdState_1929_ = crate::leanh::lean_ctor_get(v___x_1928_, 1);
                crate::leanh::lean_inc_ref(v_cmdState_1929_);
                crate::leanh::lean_dec(v___x_1928_);
                v_infoState_1930_ = crate::leanh::lean_ctor_get(v_cmdState_1929_, 8);
                v_env_1931_ = crate::leanh::lean_ctor_get(v_cmdState_1929_, 0);
                v_scopes_1932_ = crate::leanh::lean_ctor_get(v_cmdState_1929_, 2);
                v_usedQuotCtxts_1933_ = crate::leanh::lean_ctor_get(v_cmdState_1929_, 3);
                v_nextMacroScope_1934_ = crate::leanh::lean_ctor_get(v_cmdState_1929_, 4);
                v_maxRecDepth_1935_ = crate::leanh::lean_ctor_get(v_cmdState_1929_, 5);
                v_ngen_1936_ = crate::leanh::lean_ctor_get(v_cmdState_1929_, 6);
                v_auxDeclNGen_1937_ = crate::leanh::lean_ctor_get(v_cmdState_1929_, 7);
                v_traceState_1938_ = crate::leanh::lean_ctor_get(v_cmdState_1929_, 9);
                v_snapshotTasks_1939_ = crate::leanh::lean_ctor_get(v_cmdState_1929_, 10);
                v_isSharedCheck_1966_ = (!crate::leanh::lean_is_exclusive(v_cmdState_1929_)) as u8;
                if v_isSharedCheck_1966_ == 0 {
                    v_unused_1967_ = crate::leanh::lean_ctor_get(v_cmdState_1929_, 1);
                    crate::leanh::lean_dec(v_unused_1967_);
                    v___x_1941_ = v_cmdState_1929_;
                    v_isShared_1942_ = v_isSharedCheck_1966_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1939_);
                    crate::leanh::lean_inc(v_traceState_1938_);
                    crate::leanh::lean_inc(v_infoState_1930_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1937_);
                    crate::leanh::lean_inc(v_ngen_1936_);
                    crate::leanh::lean_inc(v_maxRecDepth_1935_);
                    crate::leanh::lean_inc(v_nextMacroScope_1934_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_1933_);
                    crate::leanh::lean_inc(v_scopes_1932_);
                    crate::leanh::lean_inc(v_env_1931_);
                    crate::leanh::lean_dec(v_cmdState_1929_);
                    v___x_1941_ = crate::leanh::lean_box(0);
                    v_isShared_1942_ = v_isSharedCheck_1966_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_1943_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1930_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1944_ = crate::leanh::lean_ctor_get(v_infoState_1930_, 0);
                v_lazyAssignment_1945_ = crate::leanh::lean_ctor_get(v_infoState_1930_, 1);
                v_isSharedCheck_1964_ = (!crate::leanh::lean_is_exclusive(v_infoState_1930_)) as u8;
                if v_isSharedCheck_1964_ == 0 {
                    v_unused_1965_ = crate::leanh::lean_ctor_get(v_infoState_1930_, 2);
                    crate::leanh::lean_dec(v_unused_1965_);
                    v___x_1947_ = v_infoState_1930_;
                    v_isShared_1948_ = v_isSharedCheck_1964_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_1945_);
                    crate::leanh::lean_inc(v_assignment_1944_);
                    crate::leanh::lean_dec(v_infoState_1930_);
                    v___x_1947_ = crate::leanh::lean_box(0);
                    v_isShared_1948_ = v_isSharedCheck_1964_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_pos_1949_ = crate::leanh::lean_ctor_get(v_parserState_1916_, 0);
                crate::leanh::lean_inc(v_pos_1949_);
                v___x_1950_ = 0usize;
                crate::leanh::lean_inc_ref(v_commands_1919_);
                v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_1926_, v___x_1950_, v_commands_1919_);
                v___x_1952_ = lean_array_get_size(v___x_1951_);
                v___x_1953_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v___x_1951_, v___x_1923_, v___x_1952_);
                crate::leanh::lean_dec_ref(v___x_1951_);
                v_trees_1954_ = l_Array_toPArray_x27___redArg(v___x_1953_);
                crate::leanh::lean_dec_ref(v___x_1953_);
                if v_isShared_1948_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1947_, 2, v_trees_1954_);
                    v___x_1956_ = v___x_1947_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1963_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_assignment_1944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_lazyAssignment_1945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 2, v_trees_1954_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1963_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_1943_,
                    );
                    v___x_1956_ = v_reuseFailAlloc_1963_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1942_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1941_, 8, v___x_1956_);
                    crate::leanh::lean_ctor_set(v___x_1941_, 1, v___y_1925_);
                    v___x_1958_ = v___x_1941_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1962_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_env_1931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___y_1925_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 2, v_scopes_1932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 3, v_usedQuotCtxts_1933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 4, v_nextMacroScope_1934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 5, v_maxRecDepth_1935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 6, v_ngen_1936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 7, v_auxDeclNGen_1937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 8, v___x_1956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 9, v_traceState_1938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 10, v_snapshotTasks_1939_);
                    v___x_1958_ = v_reuseFailAlloc_1962_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_1926_, v___x_1950_, v_commands_1919_);
                v___x_1960_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1960_, 0, v___x_1958_);
                crate::leanh::lean_ctor_set(v___x_1960_, 1, v_parserState_1916_);
                crate::leanh::lean_ctor_set(v___x_1960_, 2, v_pos_1949_);
                crate::leanh::lean_ctor_set(v___x_1960_, 3, v___x_1959_);
                v___x_1961_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_1960_);
                crate::leanh::lean_ctor_set(v___x_1961_, 1, v_inputCtx_1910_);
                crate::leanh::lean_ctor_set(v___x_1961_, 2, v_initialSnap_1911_);
                return v___x_1961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___boxed(
    mut v_inputCtx_1981_: *mut crate::leanh::LeanObject,
    mut v_initialSnap_1982_: *mut crate::leanh::LeanObject,
    mut v_t_1983_: *mut crate::leanh::LeanObject,
    mut v_commands_1984_: *mut crate::leanh::LeanObject,
    mut v_a_1985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1986_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(
        v_inputCtx_1981_,
        v_initialSnap_1982_,
        v_t_1983_,
        v_commands_1984_,
    );
    return v_res_1986_;
}
pub unsafe fn l_Lean_Elab_IO_processCommandsIncrementally(
    mut v_inputCtx_1989_: *mut crate::leanh::LeanObject,
    mut v_parserState_1990_: *mut crate::leanh::LeanObject,
    mut v_commandState_1991_: *mut crate::leanh::LeanObject,
    mut v_old_x3f_1992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v_inputCtx_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialSnap_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_old_x3f_1992_) == 0 {
                    v___x_2000_ = crate::leanh::lean_box(0);
                    v___y_1995_ = v___x_2000_;
                    state = 1;
                    continue;
                } else {
                    v_val_2001_ = crate::leanh::lean_ctor_get(v_old_x3f_1992_, 0);
                    v_isSharedCheck_2011_ =
                        (!crate::leanh::lean_is_exclusive(v_old_x3f_1992_)) as u8;
                    if v_isSharedCheck_2011_ == 0 {
                        v___x_2003_ = v_old_x3f_1992_;
                        v_isShared_2004_ = v_isSharedCheck_2011_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2001_);
                        crate::leanh::lean_dec(v_old_x3f_1992_);
                        v___x_2003_ = crate::leanh::lean_box(0);
                        v_isShared_2004_ = v_isSharedCheck_2011_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1996_ = l_Lean_Language_Lean_processCommands(
                    v_inputCtx_1989_,
                    v_parserState_1990_,
                    v_commandState_1991_,
                    v___y_1995_,
                );
                crate::leanh::lean_inc_ref(v___x_1996_);
                v___x_1997_ = lean_task_get_own(v___x_1996_);
                v___x_1998_ = l_Lean_Elab_IO_processCommandsIncrementally___closed__0;
                v___x_1999_ =
                    l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(
                        v_inputCtx_1989_,
                        v___x_1997_,
                        v___x_1996_,
                        v___x_1998_,
                    );
                return v___x_1999_;
            }
            2 => {
                v_inputCtx_2005_ = crate::leanh::lean_ctor_get(v_val_2001_, 1);
                crate::leanh::lean_inc_ref(v_inputCtx_2005_);
                v_initialSnap_2006_ = crate::leanh::lean_ctor_get(v_val_2001_, 2);
                crate::leanh::lean_inc_ref(v_initialSnap_2006_);
                crate::leanh::lean_dec(v_val_2001_);
                v___x_2007_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2007_, 0, v_inputCtx_2005_);
                crate::leanh::lean_ctor_set(v___x_2007_, 1, v_initialSnap_2006_);
                if v_isShared_2004_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2003_, 0, v___x_2007_);
                    v___x_2009_ = v___x_2003_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
                    v___x_2009_ = v_reuseFailAlloc_2010_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_1995_ = v___x_2009_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_IO_processCommandsIncrementally___boxed(
    mut v_inputCtx_2012_: *mut crate::leanh::LeanObject,
    mut v_parserState_2013_: *mut crate::leanh::LeanObject,
    mut v_commandState_2014_: *mut crate::leanh::LeanObject,
    mut v_old_x3f_2015_: *mut crate::leanh::LeanObject,
    mut v_a_2016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2017_ = l_Lean_Elab_IO_processCommandsIncrementally(
        v_inputCtx_2012_,
        v_parserState_2013_,
        v_commandState_2014_,
        v_old_x3f_2015_,
    );
    return v_res_2017_;
}
pub unsafe fn l_Lean_Elab_IO_processCommands(
    mut v_inputCtx_2018_: *mut crate::leanh::LeanObject,
    mut v_parserState_2019_: *mut crate::leanh::LeanObject,
    mut v_commandState_2020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toState_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2022_ = crate::leanh::lean_box(0);
    v___x_2023_ = l_Lean_Elab_IO_processCommandsIncrementally(
        v_inputCtx_2018_,
        v_parserState_2019_,
        v_commandState_2020_,
        v___x_2022_,
    );
    v_toState_2024_ = crate::leanh::lean_ctor_get(v___x_2023_, 0);
    crate::leanh::lean_inc_ref(v_toState_2024_);
    crate::leanh::lean_dec_ref(v___x_2023_);
    v___x_2025_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2025_, 0, v_toState_2024_);
    return v___x_2025_;
}
pub unsafe fn l_Lean_Elab_IO_processCommands___boxed(
    mut v_inputCtx_2026_: *mut crate::leanh::LeanObject,
    mut v_parserState_2027_: *mut crate::leanh::LeanObject,
    mut v_commandState_2028_: *mut crate::leanh::LeanObject,
    mut v_a_2029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2030_ =
        l_Lean_Elab_IO_processCommands(v_inputCtx_2026_, v_parserState_2027_, v_commandState_2028_);
    return v_res_2030_;
}
pub unsafe fn l_Lean_Elab_process(
    mut v_input_2036_: *mut crate::leanh::LeanObject,
    mut v_env_2037_: *mut crate::leanh::LeanObject,
    mut v_opts_2038_: *mut crate::leanh::LeanObject,
    mut v_fileName_2039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: u8 = 0;
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputCtx_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2053_: u8 = 0;
    let mut v_commandState_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2061_: u8 = 0;
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_fileName_2039_) == 0 {
                    v___x_2062_ = l_Lean_Elab_process___closed__1;
                    v___y_2042_ = v___x_2062_;
                    state = 1;
                    continue;
                } else {
                    v_val_2063_ = crate::leanh::lean_ctor_get(v_fileName_2039_, 0);
                    crate::leanh::lean_inc(v_val_2063_);
                    crate::leanh::lean_dec_ref_known(v_fileName_2039_, 1);
                    v___y_2042_ = v_val_2063_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2043_ = 1;
                v___x_2044_ = lean_string_utf8_byte_size(v_input_2036_);
                v_inputCtx_2045_ = l_Lean_Parser_mkInputContext___redArg(
                    v_input_2036_,
                    v___y_2042_,
                    v___x_2043_,
                    v___x_2044_,
                );
                v___x_2046_ = l_Lean_Elab_process___closed__0;
                v___x_2047_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once), _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
                v___x_2048_ = l_Lean_Elab_Command_mkState(v_env_2037_, v___x_2047_, v_opts_2038_);
                v___x_2049_ =
                    l_Lean_Elab_IO_processCommands(v_inputCtx_2045_, v___x_2046_, v___x_2048_);
                v_a_2050_ = crate::leanh::lean_ctor_get(v___x_2049_, 0);
                v_isSharedCheck_2061_ = (!crate::leanh::lean_is_exclusive(v___x_2049_)) as u8;
                if v_isSharedCheck_2061_ == 0 {
                    v___x_2052_ = v___x_2049_;
                    v_isShared_2053_ = v_isSharedCheck_2061_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2050_);
                    crate::leanh::lean_dec(v___x_2049_);
                    v___x_2052_ = crate::leanh::lean_box(0);
                    v_isShared_2053_ = v_isSharedCheck_2061_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_commandState_2054_ = crate::leanh::lean_ctor_get(v_a_2050_, 0);
                crate::leanh::lean_inc_ref(v_commandState_2054_);
                crate::leanh::lean_dec(v_a_2050_);
                v_env_2055_ = crate::leanh::lean_ctor_get(v_commandState_2054_, 0);
                crate::leanh::lean_inc_ref(v_env_2055_);
                v_messages_2056_ = crate::leanh::lean_ctor_get(v_commandState_2054_, 1);
                crate::leanh::lean_inc_ref(v_messages_2056_);
                crate::leanh::lean_dec_ref(v_commandState_2054_);
                v___x_2057_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2057_, 0, v_env_2055_);
                crate::leanh::lean_ctor_set(v___x_2057_, 1, v_messages_2056_);
                if v_isShared_2053_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2052_, 0, v___x_2057_);
                    v___x_2059_ = v___x_2052_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2060_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
                    v___x_2059_ = v_reuseFailAlloc_2060_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2059_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_process___boxed(
    mut v_input_2064_: *mut crate::leanh::LeanObject,
    mut v_env_2065_: *mut crate::leanh::LeanObject,
    mut v_opts_2066_: *mut crate::leanh::LeanObject,
    mut v_fileName_2067_: *mut crate::leanh::LeanObject,
    mut v_a_2068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2069_ = l_Lean_Elab_process(v_input_2064_, v_env_2065_, v_opts_2066_, v_fileName_2067_);
    return v_res_2069_;
}
pub unsafe fn l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(
    mut v_opts_2070_: *mut crate::leanh::LeanObject,
    mut v_opt_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2079_: u8 = 0;
    let mut v_v_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2072_ = crate::leanh::lean_ctor_get(v_opt_2071_, 0);
                v_map_2073_ = crate::leanh::lean_ctor_get(v_opts_2070_, 0);
                v___x_2074_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2073_, v_name_2072_);
                if crate::leanh::lean_obj_tag(v___x_2074_) == 0 {
                    v___x_2075_ = crate::leanh::lean_box(0);
                    return v___x_2075_;
                } else {
                    v_val_2076_ = crate::leanh::lean_ctor_get(v___x_2074_, 0);
                    v_isSharedCheck_2085_ = (!crate::leanh::lean_is_exclusive(v___x_2074_)) as u8;
                    if v_isSharedCheck_2085_ == 0 {
                        v___x_2078_ = v___x_2074_;
                        v_isShared_2079_ = v_isSharedCheck_2085_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2076_);
                        crate::leanh::lean_dec(v___x_2074_);
                        v___x_2078_ = crate::leanh::lean_box(0);
                        v_isShared_2079_ = v_isSharedCheck_2085_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_val_2076_) == 0 {
                    v_v_2080_ = crate::leanh::lean_ctor_get(v_val_2076_, 0);
                    crate::leanh::lean_inc_ref(v_v_2080_);
                    crate::leanh::lean_dec_ref_known(v_val_2076_, 1);
                    if v_isShared_2079_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2078_, 0, v_v_2080_);
                        v___x_2082_ = v___x_2078_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2083_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_v_2080_);
                        v___x_2082_ = v_reuseFailAlloc_2083_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2078_);
                    crate::leanh::lean_dec(v_val_2076_);
                    v___x_2084_ = crate::leanh::lean_box(0);
                    return v___x_2084_;
                }
            }
            2 => {
                return v___x_2082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2___boxed(
    mut v_opts_2086_: *mut crate::leanh::LeanObject,
    mut v_opt_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2088_ =
        l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(v_opts_2086_, v_opt_2087_);
    crate::leanh::lean_dec_ref(v_opt_2087_);
    crate::leanh::lean_dec_ref(v_opts_2086_);
    return v_res_2088_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(
    mut v_opts_2089_: *mut crate::leanh::LeanObject,
    mut v_opt_2090_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2091_ = crate::leanh::lean_ctor_get(v_opt_2090_, 0);
    v_defValue_2092_ = crate::leanh::lean_ctor_get(v_opt_2090_, 1);
    v_map_2093_ = crate::leanh::lean_ctor_get(v_opts_2089_, 0);
    v___x_2094_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2093_,
            v_name_2091_,
        );
    if crate::leanh::lean_obj_tag(v___x_2094_) == 0 {
        let mut v___x_2095_: u8 = 0;
        v___x_2095_ = (crate::leanh::lean_unbox(v_defValue_2092_) as u8);
        return v___x_2095_;
    } else {
        let mut v_val_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2096_ = crate::leanh::lean_ctor_get(v___x_2094_, 0);
        crate::leanh::lean_inc(v_val_2096_);
        crate::leanh::lean_dec_ref_known(v___x_2094_, 1);
        if crate::leanh::lean_obj_tag(v_val_2096_) == 1 {
            let mut v_v_2097_: u8 = 0;
            v_v_2097_ = crate::leanh::lean_ctor_get_uint8(v_val_2096_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2096_, 0);
            return v_v_2097_;
        } else {
            let mut v___x_2098_: u8 = 0;
            crate::leanh::lean_dec(v_val_2096_);
            v___x_2098_ = (crate::leanh::lean_unbox(v_defValue_2092_) as u8);
            return v___x_2098_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4___boxed(
    mut v_opts_2099_: *mut crate::leanh::LeanObject,
    mut v_opt_2100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2101_: u8 = 0;
    let mut v_r_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2101_ =
        l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(v_opts_2099_, v_opt_2100_);
    crate::leanh::lean_dec_ref(v_opt_2100_);
    crate::leanh::lean_dec_ref(v_opts_2099_);
    v_r_2102_ = crate::leanh::lean_box((v_res_2101_) as usize);
    return v_r_2102_;
}
pub unsafe fn l_Lean_Elab_runFrontend___lam__0(
    mut v_x_2103_: *mut crate::leanh::LeanObject,
    mut v_x_2104_: *mut crate::leanh::LeanObject,
    mut v_hOpt_2105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_hOpt_2105_);
    return v_hOpt_2105_;
}
pub unsafe fn l_Lean_Elab_runFrontend___lam__0___boxed(
    mut v_x_2106_: *mut crate::leanh::LeanObject,
    mut v_x_2107_: *mut crate::leanh::LeanObject,
    mut v_hOpt_2108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2109_ = l_Lean_Elab_runFrontend___lam__0(v_x_2106_, v_x_2107_, v_hOpt_2108_);
    crate::leanh::lean_dec_ref(v_hOpt_2108_);
    crate::leanh::lean_dec_ref(v_x_2107_);
    crate::leanh::lean_dec(v_x_2106_);
    return v_res_2109_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(
    mut v_as_2110_: *mut crate::leanh::LeanObject,
    mut v_i_2111_: usize,
    mut v_stop_2112_: usize,
    mut v_b_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2115_: u8 = 0;
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: usize = 0;
    let mut v___x_2120_: usize = 0;
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2115_ = lean_usize_dec_eq(v_i_2111_, v_stop_2112_);
                if v___x_2115_ == 0 {
                    v___x_2116_ = lean_array_uget_borrowed(v_as_2110_, v_i_2111_);
                    crate::leanh::lean_inc(v___x_2116_);
                    v___x_2117_ = lean_load_dynlib(v___x_2116_);
                    if crate::leanh::lean_obj_tag(v___x_2117_) == 0 {
                        v_a_2118_ = crate::leanh::lean_ctor_get(v___x_2117_, 0);
                        crate::leanh::lean_inc(v_a_2118_);
                        crate::leanh::lean_dec_ref_known(v___x_2117_, 1);
                        v___x_2119_ = 1usize;
                        v___x_2120_ = lean_usize_add(v_i_2111_, v___x_2119_);
                        v_i_2111_ = v___x_2120_;
                        v_b_2113_ = v_a_2118_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2117_;
                    }
                } else {
                    v___x_2122_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2122_, 0, v_b_2113_);
                    return v___x_2122_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(
    mut v_as_2123_: *mut crate::leanh::LeanObject,
    mut v_i_2124_: *mut crate::leanh::LeanObject,
    mut v_stop_2125_: *mut crate::leanh::LeanObject,
    mut v_b_2126_: *mut crate::leanh::LeanObject,
    mut v___y_2127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2128_: usize = 0;
    let mut v_stop_boxed_2129_: usize = 0;
    let mut v_res_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2128_ = crate::leanh::lean_unbox_usize(v_i_2124_);
    crate::leanh::lean_dec(v_i_2124_);
    v_stop_boxed_2129_ = crate::leanh::lean_unbox_usize(v_stop_2125_);
    crate::leanh::lean_dec(v_stop_2125_);
    v_res_2130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_2123_, v_i_boxed_2128_, v_stop_boxed_2129_, v_b_2126_);
    crate::leanh::lean_dec_ref(v_as_2123_);
    return v_res_2130_;
}
pub unsafe fn l_Lean_Elab_runFrontend___lam__1(
    mut v_setup_x3f_2131_: *mut crate::leanh::LeanObject,
    mut v___f_2132_: *mut crate::leanh::LeanObject,
    mut v___x_2133_: *mut crate::leanh::LeanObject,
    mut v_plugins_2134_: *mut crate::leanh::LeanObject,
    mut v_trustLevel_2135_: u32,
    mut v___x_2136_: u8,
    mut v_mainModuleName_2137_: *mut crate::leanh::LeanObject,
    mut v_stx_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2143_: u8 = 0;
    let mut v___y_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_x3f_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_2158_: u8 = 0;
    let mut v_imports_x3f_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_importArts_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: u8 = 0;
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2178_: u8 = 0;
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: u8 = 0;
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: u8 = 0;
    let mut v___x_2184_: usize = 0;
    let mut v___x_2185_: usize = 0;
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: usize = 0;
    let mut v___x_2188_: usize = 0;
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: u8 = 0;
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_setup_x3f_2131_) == 1 {
                    crate::leanh::lean_dec(v_mainModuleName_2137_);
                    v_val_2155_ = crate::leanh::lean_ctor_get(v_setup_x3f_2131_, 0);
                    crate::leanh::lean_inc(v_val_2155_);
                    crate::leanh::lean_dec_ref_known(v_setup_x3f_2131_, 1);
                    v_name_2156_ = crate::leanh::lean_ctor_get(v_val_2155_, 0);
                    crate::leanh::lean_inc(v_name_2156_);
                    v_package_x3f_2157_ = crate::leanh::lean_ctor_get(v_val_2155_, 1);
                    crate::leanh::lean_inc(v_package_x3f_2157_);
                    v_isModule_2158_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_2155_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    );
                    v_imports_x3f_2159_ = crate::leanh::lean_ctor_get(v_val_2155_, 2);
                    crate::leanh::lean_inc(v_imports_x3f_2159_);
                    v_importArts_2160_ = crate::leanh::lean_ctor_get(v_val_2155_, 3);
                    crate::leanh::lean_inc(v_importArts_2160_);
                    v_dynlibs_2161_ = crate::leanh::lean_ctor_get(v_val_2155_, 4);
                    crate::leanh::lean_inc_ref(v_dynlibs_2161_);
                    v_plugins_2162_ = crate::leanh::lean_ctor_get(v_val_2155_, 5);
                    crate::leanh::lean_inc_ref(v_plugins_2162_);
                    v_options_2163_ = crate::leanh::lean_ctor_get(v_val_2155_, 6);
                    crate::leanh::lean_inc(v_options_2163_);
                    crate::leanh::lean_dec(v_val_2155_);
                    v___x_2179_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2180_ = lean_array_get_size(v_dynlibs_2161_);
                    v___x_2181_ = lean_nat_dec_lt(v___x_2179_, v___x_2180_);
                    if v___x_2181_ == 0 {
                        crate::leanh::lean_dec_ref(v_dynlibs_2161_);
                        state = 2;
                        continue;
                    } else {
                        v___x_2182_ = crate::leanh::lean_box(0);
                        v___x_2183_ = lean_nat_dec_le(v___x_2180_, v___x_2180_);
                        if v___x_2183_ == 0 {
                            if v___x_2181_ == 0 {
                                crate::leanh::lean_dec_ref(v_dynlibs_2161_);
                                state = 2;
                                continue;
                            } else {
                                v___x_2184_ = 0usize;
                                v___x_2185_ = lean_usize_of_nat(v___x_2180_);
                                v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2161_, v___x_2184_, v___x_2185_, v___x_2182_);
                                crate::leanh::lean_dec_ref(v_dynlibs_2161_);
                                v___y_2170_ = v___x_2186_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_2187_ = 0usize;
                            v___x_2188_ = lean_usize_of_nat(v___x_2180_);
                            v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2161_, v___x_2187_, v___x_2188_, v___x_2182_);
                            crate::leanh::lean_dec_ref(v_dynlibs_2161_);
                            v___y_2170_ = v___x_2189_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_2132_);
                    crate::leanh::lean_dec(v_setup_x3f_2131_);
                    v___x_2190_ = crate::leanh::lean_box(0);
                    v___x_2191_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2138_);
                    v___x_2192_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2138_, v___x_2136_);
                    v___x_2193_ = crate::leanh::lean_box(1);
                    v___x_2194_ = crate::leanh::lean_alloc_ctor(0, 6, (5) as u32);
                    crate::leanh::lean_ctor_set(v___x_2194_, 0, v_mainModuleName_2137_);
                    crate::leanh::lean_ctor_set(v___x_2194_, 1, v___x_2190_);
                    crate::leanh::lean_ctor_set(v___x_2194_, 2, v___x_2192_);
                    crate::leanh::lean_ctor_set(v___x_2194_, 3, v___x_2133_);
                    crate::leanh::lean_ctor_set(v___x_2194_, 4, v___x_2193_);
                    crate::leanh::lean_ctor_set(v___x_2194_, 5, v_plugins_2134_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2194_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6 + 4) as u32,
                        v___x_2191_,
                    );
                    crate::leanh::lean_ctor_set_uint32(
                        v___x_2194_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        v_trustLevel_2135_,
                    );
                    v___x_2195_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2195_, 0, v___x_2194_);
                    v___x_2196_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2196_, 0, v___x_2195_);
                    return v___x_2196_;
                }
            }
            1 => {
                v___x_2149_ = l_Lean_LeanOptions_toOptions(v___y_2146_);
                v___x_2150_ = l_Lean_Options_mergeBy(v___f_2132_, v___x_2133_, v___x_2149_);
                v___x_2151_ = l_Array_append___redArg(v_plugins_2134_, v___y_2142_);
                crate::leanh::lean_dec_ref(v___y_2142_);
                v___x_2152_ = crate::leanh::lean_alloc_ctor(0, 6, (5) as u32);
                crate::leanh::lean_ctor_set(v___x_2152_, 0, v___y_2145_);
                crate::leanh::lean_ctor_set(v___x_2152_, 1, v___y_2144_);
                crate::leanh::lean_ctor_set(v___x_2152_, 2, v___y_2148_);
                crate::leanh::lean_ctor_set(v___x_2152_, 3, v___x_2150_);
                crate::leanh::lean_ctor_set(v___x_2152_, 4, v___y_2147_);
                crate::leanh::lean_ctor_set(v___x_2152_, 5, v___x_2151_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2152_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6 + 4) as u32,
                    v___y_2143_,
                );
                crate::leanh::lean_ctor_set_uint32(
                    v___x_2152_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                    v_trustLevel_2135_,
                );
                v___x_2153_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2153_, 0, v___x_2152_);
                v___x_2154_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2154_, 0, v___x_2153_);
                return v___x_2154_;
            }
            2 => {
                v___x_2165_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2138_);
                v___x_2166_ = lean_strict_or(v_isModule_2158_, v___x_2165_);
                if crate::leanh::lean_obj_tag(v_imports_x3f_2159_) == 0 {
                    v___x_2167_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2138_, v___x_2136_);
                    v___y_2142_ = v_plugins_2162_;
                    v___y_2143_ = v___x_2166_;
                    v___y_2144_ = v_package_x3f_2157_;
                    v___y_2145_ = v_name_2156_;
                    v___y_2146_ = v_options_2163_;
                    v___y_2147_ = v_importArts_2160_;
                    v___y_2148_ = v___x_2167_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_stx_2138_);
                    v_val_2168_ = crate::leanh::lean_ctor_get(v_imports_x3f_2159_, 0);
                    crate::leanh::lean_inc(v_val_2168_);
                    crate::leanh::lean_dec_ref_known(v_imports_x3f_2159_, 1);
                    v___y_2142_ = v_plugins_2162_;
                    v___y_2143_ = v___x_2166_;
                    v___y_2144_ = v_package_x3f_2157_;
                    v___y_2145_ = v_name_2156_;
                    v___y_2146_ = v_options_2163_;
                    v___y_2147_ = v_importArts_2160_;
                    v___y_2148_ = v_val_2168_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_2170_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2170_, 1);
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_options_2163_);
                    crate::leanh::lean_dec_ref(v_plugins_2162_);
                    crate::leanh::lean_dec(v_importArts_2160_);
                    crate::leanh::lean_dec(v_imports_x3f_2159_);
                    crate::leanh::lean_dec(v_package_x3f_2157_);
                    crate::leanh::lean_dec(v_name_2156_);
                    crate::leanh::lean_dec(v_stx_2138_);
                    crate::leanh::lean_dec_ref(v_plugins_2134_);
                    crate::leanh::lean_dec_ref(v___x_2133_);
                    crate::leanh::lean_dec_ref(v___f_2132_);
                    v_a_2171_ = crate::leanh::lean_ctor_get(v___y_2170_, 0);
                    v_isSharedCheck_2178_ = (!crate::leanh::lean_is_exclusive(v___y_2170_)) as u8;
                    if v_isSharedCheck_2178_ == 0 {
                        v___x_2173_ = v___y_2170_;
                        v_isShared_2174_ = v_isSharedCheck_2178_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2171_);
                        crate::leanh::lean_dec(v___y_2170_);
                        v___x_2173_ = crate::leanh::lean_box(0);
                        v_isShared_2174_ = v_isSharedCheck_2178_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2174_ == 0 {
                    v___x_2176_ = v___x_2173_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
                    v___x_2176_ = v_reuseFailAlloc_2177_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_runFrontend___lam__1___boxed(
    mut v_setup_x3f_2197_: *mut crate::leanh::LeanObject,
    mut v___f_2198_: *mut crate::leanh::LeanObject,
    mut v___x_2199_: *mut crate::leanh::LeanObject,
    mut v_plugins_2200_: *mut crate::leanh::LeanObject,
    mut v_trustLevel_2201_: *mut crate::leanh::LeanObject,
    mut v___x_2202_: *mut crate::leanh::LeanObject,
    mut v_mainModuleName_2203_: *mut crate::leanh::LeanObject,
    mut v_stx_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_trustLevel_boxed_2207_: u32 = 0;
    let mut v___x_4824__boxed_2208_: u8 = 0;
    let mut v_res_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_trustLevel_boxed_2207_ = crate::leanh::lean_unbox_uint32(v_trustLevel_2201_);
    crate::leanh::lean_dec(v_trustLevel_2201_);
    v___x_4824__boxed_2208_ = (crate::leanh::lean_unbox(v___x_2202_) as u8);
    v_res_2209_ = l_Lean_Elab_runFrontend___lam__1(
        v_setup_x3f_2197_,
        v___f_2198_,
        v___x_2199_,
        v_plugins_2200_,
        v_trustLevel_boxed_2207_,
        v___x_4824__boxed_2208_,
        v_mainModuleName_2203_,
        v_stx_2204_,
        v___y_2205_,
    );
    crate::leanh::lean_dec_ref(v___y_2205_);
    return v_res_2209_;
}
pub unsafe fn l_Lean_Elab_runFrontend___lam__2(
    mut v_s_2212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2213_ = l_Lean_Elab_runFrontend___lam__2___closed__0;
    v___x_2214_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2214_, 0, v_s_2212_);
    crate::leanh::lean_ctor_set(v___x_2214_, 1, v___x_2213_);
    return v___x_2214_;
}
pub unsafe fn l_Lean_Elab_runFrontend___lam__3(
    mut v_env_2215_: *mut crate::leanh::LeanObject,
    mut v___y_2216_: *mut crate::leanh::LeanObject,
    mut v_opts_2217_: *mut crate::leanh::LeanObject,
    mut v_val_2218_: *mut crate::leanh::LeanObject,
    mut v___x_2219_: u8,
    mut v_a_2220_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: u8 = 0;
    v___x_2222_ = l_Lean_Linter_recordLints(v_env_2215_, v___y_2216_);
    v___x_2223_ = l_Lean_Compiler_compiler_postponeCompile;
    v___x_2224_ =
        l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(v_opts_2217_, v___x_2223_);
    if v___x_2224_ == 0 {
        let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2225_ = l_Lean_writeModule(v___x_2222_, v_val_2218_, v___x_2219_);
        return v___x_2225_;
    } else {
        let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2226_ = l_Lean_writeModule(v___x_2222_, v_val_2218_, v_a_2220_);
        return v___x_2226_;
    }
}
pub unsafe fn l_Lean_Elab_runFrontend___lam__3___boxed(
    mut v_env_2227_: *mut crate::leanh::LeanObject,
    mut v___y_2228_: *mut crate::leanh::LeanObject,
    mut v_opts_2229_: *mut crate::leanh::LeanObject,
    mut v_val_2230_: *mut crate::leanh::LeanObject,
    mut v___x_2231_: *mut crate::leanh::LeanObject,
    mut v_a_2232_: *mut crate::leanh::LeanObject,
    mut v___y_2233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4946__boxed_2234_: u8 = 0;
    let mut v_a_4947__boxed_2235_: u8 = 0;
    let mut v_res_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4946__boxed_2234_ = (crate::leanh::lean_unbox(v___x_2231_) as u8);
    v_a_4947__boxed_2235_ = (crate::leanh::lean_unbox(v_a_2232_) as u8);
    v_res_2236_ = l_Lean_Elab_runFrontend___lam__3(
        v_env_2227_,
        v___y_2228_,
        v_opts_2229_,
        v_val_2230_,
        v___x_4946__boxed_2234_,
        v_a_4947__boxed_2235_,
    );
    crate::leanh::lean_dec_ref(v_opts_2229_);
    return v_res_2236_;
}
pub unsafe fn l_Lean_Elab_runFrontend___lam__5(
    mut v___f_2238_: *mut crate::leanh::LeanObject,
    mut v_s_2239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSnapshot_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_metaSnap_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_x3f_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2258_: u8 = 0;
    let mut v_firstCmdSnap_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: u8 = 0;
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_2240_ = crate::leanh::lean_ctor_get(v_s_2239_, 0);
                crate::leanh::lean_inc_ref(v_toSnapshot_2240_);
                v_metaSnap_2241_ = crate::leanh::lean_ctor_get(v_s_2239_, 1);
                crate::leanh::lean_inc_ref(v_metaSnap_2241_);
                v_result_x3f_2242_ = crate::leanh::lean_ctor_get(v_s_2239_, 2);
                crate::leanh::lean_inc(v_result_x3f_2242_);
                crate::leanh::lean_dec_ref(v_s_2239_);
                if crate::leanh::lean_obj_tag(v_result_x3f_2242_) == 0 {
                    v___x_2254_ = crate::leanh::lean_box(0);
                    v___y_2244_ = v___x_2254_;
                    state = 1;
                    continue;
                } else {
                    v_val_2255_ = crate::leanh::lean_ctor_get(v_result_x3f_2242_, 0);
                    v_isSharedCheck_2268_ =
                        (!crate::leanh::lean_is_exclusive(v_result_x3f_2242_)) as u8;
                    if v_isSharedCheck_2268_ == 0 {
                        v___x_2257_ = v_result_x3f_2242_;
                        v_isShared_2258_ = v_isSharedCheck_2268_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2255_);
                        crate::leanh::lean_dec(v_result_x3f_2242_);
                        v___x_2257_ = crate::leanh::lean_box(0);
                        v_isShared_2258_ = v_isSharedCheck_2268_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_stx_x3f_2245_ = crate::leanh::lean_ctor_get(v_metaSnap_2241_, 0);
                crate::leanh::lean_inc(v_stx_x3f_2245_);
                v_reportingRange_2246_ = crate::leanh::lean_ctor_get(v_metaSnap_2241_, 1);
                crate::leanh::lean_inc(v_reportingRange_2246_);
                v___x_2247_ = 1;
                v___x_2248_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_metaSnap_2241_,
                    v___f_2238_,
                    v_stx_x3f_2245_,
                    v_reportingRange_2246_,
                    v___x_2247_,
                );
                v___x_2249_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2250_ = lean_mk_empty_array_with_capacity(v___x_2249_);
                v___x_2251_ = lean_array_push(v___x_2250_, v___x_2248_);
                v___x_2252_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2244_, v___x_2251_);
                v___x_2253_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2253_, 0, v_toSnapshot_2240_);
                crate::leanh::lean_ctor_set(v___x_2253_, 1, v___x_2252_);
                return v___x_2253_;
            }
            2 => {
                v_firstCmdSnap_2259_ = crate::leanh::lean_ctor_get(v_val_2255_, 1);
                crate::leanh::lean_inc_ref(v_firstCmdSnap_2259_);
                crate::leanh::lean_dec(v_val_2255_);
                v_stx_x3f_2260_ = crate::leanh::lean_ctor_get(v_firstCmdSnap_2259_, 0);
                crate::leanh::lean_inc(v_stx_x3f_2260_);
                v_reportingRange_2261_ = crate::leanh::lean_ctor_get(v_firstCmdSnap_2259_, 1);
                crate::leanh::lean_inc(v_reportingRange_2261_);
                v___x_2262_ = l_Lean_Elab_runFrontend___lam__5___closed__0;
                v___x_2263_ = 1;
                v___x_2264_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_firstCmdSnap_2259_,
                    v___x_2262_,
                    v_stx_x3f_2260_,
                    v_reportingRange_2261_,
                    v___x_2263_,
                );
                if v_isShared_2258_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2257_, 0, v___x_2264_);
                    v___x_2266_ = v___x_2257_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2267_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
                    v___x_2266_ = v_reuseFailAlloc_2267_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_2244_ = v___x_2266_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(
    mut v_o_2272_: *mut crate::leanh::LeanObject,
    mut v_k_2273_: *mut crate::leanh::LeanObject,
    mut v_v_2274_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2276_: u8 = 0;
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: u8 = 0;
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_2275_ = crate::leanh::lean_ctor_get(v_o_2272_, 0);
                v_hasTrace_2276_ = crate::leanh::lean_ctor_get_uint8(
                    v_o_2272_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2290_ = (!crate::leanh::lean_is_exclusive(v_o_2272_)) as u8;
                if v_isSharedCheck_2290_ == 0 {
                    v___x_2278_ = v_o_2272_;
                    v_isShared_2279_ = v_isSharedCheck_2290_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_2275_);
                    crate::leanh::lean_dec(v_o_2272_);
                    v___x_2278_ = crate::leanh::lean_box(0);
                    v_isShared_2279_ = v_isSharedCheck_2290_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2280_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_2280_, 0 as u32, v_v_2274_);
                crate::leanh::lean_inc(v_k_2273_);
                v___x_2281_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2273_, v___x_2280_, v_map_2275_);
                if v_hasTrace_2276_ == 0 {
                    v___x_2282_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1;
                    v___x_2283_ = l_Lean_Name_isPrefixOf(v___x_2282_, v_k_2273_);
                    crate::leanh::lean_dec(v_k_2273_);
                    if v_isShared_2279_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2278_, 0, v___x_2281_);
                        v___x_2285_ = v___x_2278_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2286_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2281_);
                        v___x_2285_ = v_reuseFailAlloc_2286_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_2273_);
                    if v_isShared_2279_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2278_, 0, v___x_2281_);
                        v___x_2288_ = v___x_2278_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2289_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2281_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2289_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_2276_,
                        );
                        v___x_2288_ = v_reuseFailAlloc_2289_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2285_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2283_,
                );
                return v___x_2285_;
            }
            3 => {
                return v___x_2288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(
    mut v_o_2291_: *mut crate::leanh::LeanObject,
    mut v_k_2292_: *mut crate::leanh::LeanObject,
    mut v_v_2293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_boxed_2294_: u8 = 0;
    let mut v_res_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_2294_ = (crate::leanh::lean_unbox(v_v_2293_) as u8);
    v_res_2295_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2291_, v_k_2292_, v_v_boxed_2294_);
    return v_res_2295_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(
    mut v_opts_2296_: *mut crate::leanh::LeanObject,
    mut v_opt_2297_: *mut crate::leanh::LeanObject,
    mut v_val_2298_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2299_ = crate::leanh::lean_ctor_get(v_opt_2297_, 0);
    crate::leanh::lean_inc(v_name_2299_);
    crate::leanh::lean_dec_ref(v_opt_2297_);
    v___x_2300_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_2296_, v_name_2299_, v_val_2298_);
    return v___x_2300_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(
    mut v_opts_2301_: *mut crate::leanh::LeanObject,
    mut v_opt_2302_: *mut crate::leanh::LeanObject,
    mut v_val_2303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_2304_: u8 = 0;
    let mut v_res_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_2304_ = (crate::leanh::lean_unbox(v_val_2303_) as u8);
    v_res_2305_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2301_, v_opt_2302_, v_val_boxed_2304_);
    return v_res_2305_;
}
pub unsafe fn l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(
    mut v_opts_2306_: *mut crate::leanh::LeanObject,
    mut v_opt_2307_: *mut crate::leanh::LeanObject,
    mut v_val_2308_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: u8 = 0;
    v_name_2309_ = crate::leanh::lean_ctor_get(v_opt_2307_, 0);
    v_map_2310_ = crate::leanh::lean_ctor_get(v_opts_2306_, 0);
    v___x_2311_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_name_2309_,
            v_map_2310_,
        );
    if v___x_2311_ == 0 {
        let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2312_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2306_, v_opt_2307_, v_val_2308_);
        return v___x_2312_;
    } else {
        crate::leanh::lean_dec_ref(v_opt_2307_);
        return v_opts_2306_;
    }
}
pub unsafe fn l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(
    mut v_opts_2313_: *mut crate::leanh::LeanObject,
    mut v_opt_2314_: *mut crate::leanh::LeanObject,
    mut v_val_2315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_2316_: u8 = 0;
    let mut v_res_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_2316_ = (crate::leanh::lean_unbox(v_val_2315_) as u8);
    v_res_2317_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(
        v_opts_2313_,
        v_opt_2314_,
        v_val_boxed_2316_,
    );
    return v_res_2317_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(
    mut v_as_2318_: *mut crate::leanh::LeanObject,
    mut v_i_2319_: usize,
    mut v_stop_2320_: usize,
    mut v_b_2321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: usize = 0;
    let mut v___x_2325_: usize = 0;
    let mut v___x_2327_: u8 = 0;
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoTree_x3f_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2327_ = lean_usize_dec_eq(v_i_2319_, v_stop_2320_);
                if v___x_2327_ == 0 {
                    v___x_2328_ = lean_array_uget_borrowed(v_as_2318_, v_i_2319_);
                    v_infoTree_x3f_2329_ = crate::leanh::lean_ctor_get(v___x_2328_, 2);
                    if crate::leanh::lean_obj_tag(v_infoTree_x3f_2329_) == 1 {
                        v_val_2330_ = crate::leanh::lean_ctor_get(v_infoTree_x3f_2329_, 0);
                        v___x_2331_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2332_ = lean_mk_empty_array_with_capacity(v___x_2331_);
                        crate::leanh::lean_inc(v_val_2330_);
                        v___x_2333_ = lean_array_push(v___x_2332_, v_val_2330_);
                        v___x_2334_ = l_Array_append___redArg(v_b_2321_, v___x_2333_);
                        crate::leanh::lean_dec_ref(v___x_2333_);
                        v___y_2323_ = v___x_2334_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2335_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0;
                        v___x_2336_ = l_Array_append___redArg(v_b_2321_, v___x_2335_);
                        v___y_2323_ = v___x_2336_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2321_;
                }
            }
            1 => {
                v___x_2324_ = 1usize;
                v___x_2325_ = lean_usize_add(v_i_2319_, v___x_2324_);
                v_i_2319_ = v___x_2325_;
                v_b_2321_ = v___y_2323_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5___boxed(
    mut v_as_2337_: *mut crate::leanh::LeanObject,
    mut v_i_2338_: *mut crate::leanh::LeanObject,
    mut v_stop_2339_: *mut crate::leanh::LeanObject,
    mut v_b_2340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2341_: usize = 0;
    let mut v_stop_boxed_2342_: usize = 0;
    let mut v_res_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2341_ = crate::leanh::lean_unbox_usize(v_i_2338_);
    crate::leanh::lean_dec(v_i_2338_);
    v_stop_boxed_2342_ = crate::leanh::lean_unbox_usize(v_stop_2339_);
    crate::leanh::lean_dec(v_stop_2339_);
    v_res_2343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(v_as_2337_, v_i_boxed_2341_, v_stop_boxed_2342_, v_b_2340_);
    crate::leanh::lean_dec_ref(v_as_2337_);
    return v_res_2343_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(
    mut v_as_2344_: *mut crate::leanh::LeanObject,
    mut v_i_2345_: usize,
    mut v_stop_2346_: usize,
    mut v_b_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2348_: u8 = 0;
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgLog_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: usize = 0;
    let mut v___x_2354_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2348_ = lean_usize_dec_eq(v_i_2345_, v_stop_2346_);
                if v___x_2348_ == 0 {
                    v___x_2349_ = lean_array_uget_borrowed(v_as_2344_, v_i_2345_);
                    v_diagnostics_2350_ = crate::leanh::lean_ctor_get(v___x_2349_, 1);
                    v_msgLog_2351_ = crate::leanh::lean_ctor_get(v_diagnostics_2350_, 0);
                    crate::leanh::lean_inc_ref(v_msgLog_2351_);
                    v___x_2352_ = l_Lean_MessageLog_append(v_b_2347_, v_msgLog_2351_);
                    v___x_2353_ = 1usize;
                    v___x_2354_ = lean_usize_add(v_i_2345_, v___x_2353_);
                    v_i_2345_ = v___x_2354_;
                    v_b_2347_ = v___x_2352_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2347_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6___boxed(
    mut v_as_2356_: *mut crate::leanh::LeanObject,
    mut v_i_2357_: *mut crate::leanh::LeanObject,
    mut v_stop_2358_: *mut crate::leanh::LeanObject,
    mut v_b_2359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2360_: usize = 0;
    let mut v_stop_boxed_2361_: usize = 0;
    let mut v_res_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2360_ = crate::leanh::lean_unbox_usize(v_i_2357_);
    crate::leanh::lean_dec(v_i_2357_);
    v_stop_boxed_2361_ = crate::leanh::lean_unbox_usize(v_stop_2358_);
    crate::leanh::lean_dec(v_stop_2358_);
    v_res_2362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v_as_2356_, v_i_boxed_2360_, v_stop_boxed_2361_, v_b_2359_);
    crate::leanh::lean_dec_ref(v_as_2356_);
    return v_res_2362_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(
    mut v_sz_2363_: usize,
    mut v_i_2364_: usize,
    mut v_bs_2365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2366_: u8 = 0;
    let mut v_v_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: usize = 0;
    let mut v___x_2372_: usize = 0;
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2366_ = lean_usize_dec_lt(v_i_2364_, v_sz_2363_);
                if v___x_2366_ == 0 {
                    return v_bs_2365_;
                } else {
                    v_v_2367_ = lean_array_uget_borrowed(v_bs_2365_, v_i_2364_);
                    v_traces_2368_ = crate::leanh::lean_ctor_get(v_v_2367_, 3);
                    crate::leanh::lean_inc_ref(v_traces_2368_);
                    v___x_2369_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2370_ = lean_array_uset(v_bs_2365_, v_i_2364_, v___x_2369_);
                    v___x_2371_ = 1usize;
                    v___x_2372_ = lean_usize_add(v_i_2364_, v___x_2371_);
                    v___x_2373_ = lean_array_uset(v_bs_x27_2370_, v_i_2364_, v_traces_2368_);
                    v_i_2364_ = v___x_2372_;
                    v_bs_2365_ = v___x_2373_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3___boxed(
    mut v_sz_2375_: *mut crate::leanh::LeanObject,
    mut v_i_2376_: *mut crate::leanh::LeanObject,
    mut v_bs_2377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2378_: usize = 0;
    let mut v_i_boxed_2379_: usize = 0;
    let mut v_res_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2378_ = crate::leanh::lean_unbox_usize(v_sz_2375_);
    crate::leanh::lean_dec(v_sz_2375_);
    v_i_boxed_2379_ = crate::leanh::lean_unbox_usize(v_i_2376_);
    crate::leanh::lean_dec(v_i_2376_);
    v_res_2380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_boxed_2378_, v_i_boxed_2379_, v_bs_2377_);
    return v_res_2380_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(
    mut v_as_2381_: *mut crate::leanh::LeanObject,
    mut v_i_2382_: usize,
    mut v_stop_2383_: usize,
    mut v_b_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2385_: u8 = 0;
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: usize = 0;
    let mut v___x_2391_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2385_ = lean_usize_dec_eq(v_i_2382_, v_stop_2383_);
                if v___x_2385_ == 0 {
                    v___x_2386_ = lean_array_uget_borrowed(v_as_2381_, v_i_2382_);
                    v___x_2387_ = 2;
                    v___x_2388_ = crate::leanh::lean_box((v___x_2387_) as usize);
                    crate::leanh::lean_inc(v___x_2386_);
                    v___x_2389_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2386_, v___x_2388_, v_b_2384_);
                    v___x_2390_ = 1usize;
                    v___x_2391_ = lean_usize_add(v_i_2382_, v___x_2390_);
                    v_i_2382_ = v___x_2391_;
                    v_b_2384_ = v___x_2389_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2384_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(
    mut v_as_2393_: *mut crate::leanh::LeanObject,
    mut v_i_2394_: *mut crate::leanh::LeanObject,
    mut v_stop_2395_: *mut crate::leanh::LeanObject,
    mut v_b_2396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2397_: usize = 0;
    let mut v_stop_boxed_2398_: usize = 0;
    let mut v_res_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2397_ = crate::leanh::lean_unbox_usize(v_i_2394_);
    crate::leanh::lean_dec(v_i_2394_);
    v_stop_boxed_2398_ = crate::leanh::lean_unbox_usize(v_stop_2395_);
    crate::leanh::lean_dec(v_stop_2395_);
    v_res_2399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_2393_, v_i_boxed_2397_, v_stop_boxed_2398_, v_b_2396_);
    crate::leanh::lean_dec_ref(v_as_2393_);
    return v_res_2399_;
}
pub unsafe fn _init_l_Lean_Elab_runFrontend___closed__2() -> f64 {
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: f64 = 0.0;
    v___x_2402_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_2403_ = lean_float_of_nat(v___x_2402_);
    return v___x_2403_;
}
pub unsafe fn l_Lean_Elab_runFrontend(
    mut v_input_2407_: *mut crate::leanh::LeanObject,
    mut v_opts_2408_: *mut crate::leanh::LeanObject,
    mut v_fileName_2409_: *mut crate::leanh::LeanObject,
    mut v_mainModuleName_2410_: *mut crate::leanh::LeanObject,
    mut v_trustLevel_2411_: u32,
    mut v_oleanFileName_x3f_2412_: *mut crate::leanh::LeanObject,
    mut v_ileanFileName_x3f_2413_: *mut crate::leanh::LeanObject,
    mut v_jsonOutput_2414_: u8,
    mut v_errorOnKinds_2415_: *mut crate::leanh::LeanObject,
    mut v_plugins_2416_: *mut crate::leanh::LeanObject,
    mut v_printStats_2417_: u8,
    mut v_setup_x3f_2418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: u8 = 0;
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSnapshot_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_metaSnap_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_x3f_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: f64 = 0.0;
    let mut v___x_2447_: f64 = 0.0;
    let mut v___x_2448_: f64 = 0.0;
    let mut v___y_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2457_: usize = 0;
    let mut v___x_2458_: usize = 0;
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut v_a_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2477_: u8 = 0;
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2481_: u8 = 0;
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: u8 = 0;
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2485_: usize = 0;
    let mut v___x_2486_: usize = 0;
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut v_a_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2509_: u8 = 0;
    let mut v___y_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: u8 = 0;
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2531_: u8 = 0;
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2535_: u8 = 0;
    let mut v___y_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2546_: u8 = 0;
    let mut v___x_2547_: usize = 0;
    let mut v___x_2548_: usize = 0;
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: usize = 0;
    let mut v___x_2551_: usize = 0;
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2555_: u8 = 0;
    let mut v___y_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut v___y_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2579_: u8 = 0;
    let mut v___y_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2582_: u8 = 0;
    let mut v___y_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: u8 = 0;
    let mut v___x_2591_: u8 = 0;
    let mut v___x_2592_: usize = 0;
    let mut v___x_2593_: usize = 0;
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: usize = 0;
    let mut v___x_2596_: usize = 0;
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u8 = 0;
    let mut v___x_2615_: u8 = 0;
    let mut v_opts_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: u8 = 0;
    let mut v___x_2619_: u8 = 0;
    let mut v_a_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2623_: u8 = 0;
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2627_: u8 = 0;
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2631_: u8 = 0;
    let mut v_a_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2639_: u8 = 0;
    let mut v___y_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: u8 = 0;
    let mut v___x_2654_: u8 = 0;
    let mut v___x_2655_: usize = 0;
    let mut v___x_2656_: usize = 0;
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: usize = 0;
    let mut v___x_2659_: usize = 0;
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v_processedSnap_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2673_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2426_ = lean_io_mono_nanos_now();
                v___f_2427_ = l_Lean_Elab_runFrontend___closed__0;
                v___x_2428_ = 1;
                v___x_2429_ = lean_string_utf8_byte_size(v_input_2407_);
                v___x_2430_ = l_Lean_Parser_mkInputContext___redArg(
                    v_input_2407_,
                    v_fileName_2409_,
                    v___x_2428_,
                    v___x_2429_,
                );
                v___x_2431_ = l_Lean_internal_cmdlineSnapshots;
                v___x_2432_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(
                    v_opts_2408_,
                    v___x_2431_,
                    v___x_2428_,
                );
                v___x_2433_ = l_Lean_Elab_async;
                v___x_2434_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(
                    v___x_2432_,
                    v___x_2433_,
                    v___x_2428_,
                );
                v___x_2435_ = crate::leanh::lean_box_uint32(v_trustLevel_2411_);
                v___x_2436_ = crate::leanh::lean_box((v___x_2428_) as usize);
                crate::leanh::lean_inc(v_mainModuleName_2410_);
                crate::leanh::lean_inc_ref(v___x_2434_);
                v___f_2437_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_runFrontend___lam__1___boxed as *mut core::ffi::c_void,
                    10,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_2437_, 0, v_setup_x3f_2418_);
                crate::leanh::lean_closure_set(v___f_2437_, 1, v___f_2427_);
                crate::leanh::lean_closure_set(v___f_2437_, 2, v___x_2434_);
                crate::leanh::lean_closure_set(v___f_2437_, 3, v_plugins_2416_);
                crate::leanh::lean_closure_set(v___f_2437_, 4, v___x_2435_);
                crate::leanh::lean_closure_set(v___f_2437_, 5, v___x_2436_);
                crate::leanh::lean_closure_set(v___f_2437_, 6, v_mainModuleName_2410_);
                v___x_2438_ = crate::leanh::lean_box(0);
                v___x_2439_ = l_Lean_Language_Lean_process(v___f_2437_, v___x_2438_, v___x_2430_);
                v_toSnapshot_2440_ = crate::leanh::lean_ctor_get(v___x_2439_, 0);
                crate::leanh::lean_inc_ref(v_toSnapshot_2440_);
                v_metaSnap_2441_ = crate::leanh::lean_ctor_get(v___x_2439_, 1);
                crate::leanh::lean_inc_ref(v_metaSnap_2441_);
                v_stx_2442_ = crate::leanh::lean_ctor_get(v___x_2439_, 3);
                crate::leanh::lean_inc(v_stx_2442_);
                v_result_x3f_2443_ = crate::leanh::lean_ctor_get(v___x_2439_, 4);
                crate::leanh::lean_inc(v_result_x3f_2443_);
                v___f_2444_ = l_Lean_Elab_runFrontend___closed__1;
                v___x_2445_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_2446_ = lean_float_of_nat(v___x_2426_);
                v___x_2447_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_runFrontend___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Elab_runFrontend___closed__2_once),
                    _init_l_Lean_Elab_runFrontend___closed__2,
                );
                v___x_2448_ = lean_float_div(v___x_2446_, v___x_2447_);
                if crate::leanh::lean_obj_tag(v_result_x3f_2443_) == 0 {
                    v___y_2641_ = v___x_2438_;
                    state = 26;
                    continue;
                } else {
                    v_val_2661_ = crate::leanh::lean_ctor_get(v_result_x3f_2443_, 0);
                    v_isSharedCheck_2673_ =
                        (!crate::leanh::lean_is_exclusive(v_result_x3f_2443_)) as u8;
                    if v_isSharedCheck_2673_ == 0 {
                        v___x_2663_ = v_result_x3f_2443_;
                        v_isShared_2664_ = v_isSharedCheck_2673_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2661_);
                        crate::leanh::lean_dec(v_result_x3f_2443_);
                        v___x_2663_ = crate::leanh::lean_box(0);
                        v_isShared_2664_ = v_isSharedCheck_2673_;
                        state = 27;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2423_ = lean_runtime_forget(v___y_2421_);
                v___x_2424_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2424_, 0, v___y_2422_);
                v___x_2425_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2425_, 0, v___x_2424_);
                return v___x_2425_;
            }
            2 => {
                v___x_2453_ = l_Lean_trace_profiler_output;
                v___x_2454_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(
                    v___x_2434_,
                    v___x_2453_,
                );
                if crate::leanh::lean_obj_tag(v___x_2454_) == 1 {
                    crate::leanh::lean_dec_ref(v___y_2450_);
                    v_val_2455_ = crate::leanh::lean_ctor_get(v___x_2454_, 0);
                    crate::leanh::lean_inc(v_val_2455_);
                    crate::leanh::lean_dec_ref_known(v___x_2454_, 1);
                    crate::leanh::lean_inc_ref(v___y_2451_);
                    v___x_2456_ = l_Lean_Language_SnapshotTree_getAll(v___y_2451_);
                    v_sz_2457_ = lean_array_size(v___x_2456_);
                    v___x_2458_ = 0usize;
                    v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_2457_, v___x_2458_, v___x_2456_);
                    v___x_2460_ = l_Lean_Name_toString(v_mainModuleName_2410_, v___x_2428_);
                    v___x_2461_ = l_Lean_Firefox_Profile_export(
                        v___x_2460_,
                        v___x_2448_,
                        v___x_2459_,
                        v___x_2434_,
                    );
                    crate::leanh::lean_dec_ref(v___x_2434_);
                    crate::leanh::lean_dec_ref(v___x_2459_);
                    if crate::leanh::lean_obj_tag(v___x_2461_) == 0 {
                        v_a_2462_ = crate::leanh::lean_ctor_get(v___x_2461_, 0);
                        crate::leanh::lean_inc(v_a_2462_);
                        crate::leanh::lean_dec_ref_known(v___x_2461_, 1);
                        v___x_2463_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2462_);
                        v___x_2464_ = l_Lean_Json_compress(v___x_2463_);
                        v___x_2465_ = l_IO_FS_writeFile(v_val_2455_, v___x_2464_);
                        crate::leanh::lean_dec_ref(v___x_2464_);
                        crate::leanh::lean_dec(v_val_2455_);
                        if crate::leanh::lean_obj_tag(v___x_2465_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2465_, 1);
                            v___y_2421_ = v___y_2451_;
                            v___y_2422_ = v___y_2452_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_2452_);
                            crate::leanh::lean_dec_ref(v___y_2451_);
                            v_a_2466_ = crate::leanh::lean_ctor_get(v___x_2465_, 0);
                            v_isSharedCheck_2473_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2465_)) as u8;
                            if v_isSharedCheck_2473_ == 0 {
                                v___x_2468_ = v___x_2465_;
                                v_isShared_2469_ = v_isSharedCheck_2473_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2466_);
                                crate::leanh::lean_dec(v___x_2465_);
                                v___x_2468_ = crate::leanh::lean_box(0);
                                v_isShared_2469_ = v_isSharedCheck_2473_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2455_);
                        crate::leanh::lean_dec_ref(v___y_2452_);
                        crate::leanh::lean_dec_ref(v___y_2451_);
                        v_a_2474_ = crate::leanh::lean_ctor_get(v___x_2461_, 0);
                        v_isSharedCheck_2481_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2461_)) as u8;
                        if v_isSharedCheck_2481_ == 0 {
                            v___x_2476_ = v___x_2461_;
                            v_isShared_2477_ = v_isSharedCheck_2481_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2474_);
                            crate::leanh::lean_dec(v___x_2461_);
                            v___x_2476_ = crate::leanh::lean_box(0);
                            v_isShared_2477_ = v_isSharedCheck_2481_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2454_);
                    v___x_2482_ = l_Lean_trace_profiler_serve;
                    v___x_2483_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(
                        v___y_2450_,
                        v___x_2482_,
                    );
                    crate::leanh::lean_dec_ref(v___y_2450_);
                    if v___x_2483_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2434_);
                        crate::leanh::lean_dec(v_mainModuleName_2410_);
                        v___y_2421_ = v___y_2451_;
                        v___y_2422_ = v___y_2452_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v___y_2451_);
                        v___x_2484_ = l_Lean_Language_SnapshotTree_getAll(v___y_2451_);
                        v_sz_2485_ = lean_array_size(v___x_2484_);
                        v___x_2486_ = 0usize;
                        v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_2485_, v___x_2486_, v___x_2484_);
                        v___x_2488_ = l_Lean_Name_toString(v_mainModuleName_2410_, v___x_2428_);
                        v___x_2489_ = l_Lean_Firefox_Profile_export(
                            v___x_2488_,
                            v___x_2448_,
                            v___x_2487_,
                            v___x_2434_,
                        );
                        crate::leanh::lean_dec_ref(v___x_2434_);
                        crate::leanh::lean_dec_ref(v___x_2487_);
                        if crate::leanh::lean_obj_tag(v___x_2489_) == 0 {
                            v_a_2490_ = crate::leanh::lean_ctor_get(v___x_2489_, 0);
                            crate::leanh::lean_inc(v_a_2490_);
                            crate::leanh::lean_dec_ref_known(v___x_2489_, 1);
                            v___x_2491_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2490_);
                            v___x_2492_ = l_Lean_Json_compress(v___x_2491_);
                            v___x_2493_ = l_Lean_Firefox_Profile_serve(v___x_2492_);
                            if crate::leanh::lean_obj_tag(v___x_2493_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2493_, 1);
                                v___y_2421_ = v___y_2451_;
                                v___y_2422_ = v___y_2452_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___y_2452_);
                                crate::leanh::lean_dec_ref(v___y_2451_);
                                v_a_2494_ = crate::leanh::lean_ctor_get(v___x_2493_, 0);
                                v_isSharedCheck_2501_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2493_)) as u8;
                                if v_isSharedCheck_2501_ == 0 {
                                    v___x_2496_ = v___x_2493_;
                                    v_isShared_2497_ = v_isSharedCheck_2501_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2494_);
                                    crate::leanh::lean_dec(v___x_2493_);
                                    v___x_2496_ = crate::leanh::lean_box(0);
                                    v_isShared_2497_ = v_isSharedCheck_2501_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_2452_);
                            crate::leanh::lean_dec_ref(v___y_2451_);
                            v_a_2502_ = crate::leanh::lean_ctor_get(v___x_2489_, 0);
                            v_isSharedCheck_2509_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2489_)) as u8;
                            if v_isSharedCheck_2509_ == 0 {
                                v___x_2504_ = v___x_2489_;
                                v_isShared_2505_ = v_isSharedCheck_2509_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2502_);
                                crate::leanh::lean_dec(v___x_2489_);
                                v___x_2504_ = crate::leanh::lean_box(0);
                                v_isShared_2505_ = v_isSharedCheck_2509_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_2469_ == 0 {
                    v___x_2471_ = v___x_2468_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
                    v___x_2471_ = v_reuseFailAlloc_2472_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2471_;
            }
            5 => {
                if v_isShared_2477_ == 0 {
                    v___x_2479_ = v___x_2476_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2480_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
                    v___x_2479_ = v_reuseFailAlloc_2480_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2479_;
            }
            7 => {
                if v_isShared_2497_ == 0 {
                    v___x_2499_ = v___x_2496_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
                    v___x_2499_ = v_reuseFailAlloc_2500_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2499_;
            }
            9 => {
                if v_isShared_2505_ == 0 {
                    v___x_2507_ = v___x_2504_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2508_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
                    v___x_2507_ = v_reuseFailAlloc_2508_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2507_;
            }
            11 => {
                v_fileMap_2516_ = crate::leanh::lean_ctor_get(v___x_2430_, 2);
                crate::leanh::lean_inc_ref(v_fileMap_2516_);
                crate::leanh::lean_dec_ref(v___x_2430_);
                v___x_2517_ = 0;
                v___x_2518_ = l_Lean_Server_findModuleRefs(
                    v_fileMap_2516_,
                    v___y_2515_,
                    v___x_2517_,
                    v___x_2517_,
                );
                crate::leanh::lean_dec_ref(v___y_2515_);
                v___x_2519_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_2518_);
                v_fst_2520_ = crate::leanh::lean_ctor_get(v___x_2519_, 0);
                crate::leanh::lean_inc(v_fst_2520_);
                v_snd_2521_ = crate::leanh::lean_ctor_get(v___x_2519_, 1);
                crate::leanh::lean_inc(v_snd_2521_);
                crate::leanh::lean_dec_ref(v___x_2519_);
                v___x_2522_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_2523_ = l_Lean_Server_collectImports(v_stx_2442_);
                crate::leanh::lean_inc(v_mainModuleName_2410_);
                v___x_2524_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2524_, 0, v___x_2522_);
                crate::leanh::lean_ctor_set(v___x_2524_, 1, v_mainModuleName_2410_);
                crate::leanh::lean_ctor_set(v___x_2524_, 2, v___x_2523_);
                crate::leanh::lean_ctor_set(v___x_2524_, 3, v_fst_2520_);
                crate::leanh::lean_ctor_set(v___x_2524_, 4, v_snd_2521_);
                v___x_2525_ = l_Lean_Server_instToJsonIlean_toJson(v___x_2524_);
                v___x_2526_ = l_Lean_Json_compress(v___x_2525_);
                v___x_2527_ = l_IO_FS_writeFile(v___y_2513_, v___x_2526_);
                crate::leanh::lean_dec_ref(v___x_2526_);
                if crate::leanh::lean_obj_tag(v___x_2527_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2527_, 1);
                    v___y_2450_ = v___y_2511_;
                    v___y_2451_ = v___y_2512_;
                    v___y_2452_ = v___y_2514_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_2514_);
                    crate::leanh::lean_dec_ref(v___y_2512_);
                    crate::leanh::lean_dec_ref(v___y_2511_);
                    crate::leanh::lean_dec_ref(v___x_2434_);
                    crate::leanh::lean_dec(v_mainModuleName_2410_);
                    v_a_2528_ = crate::leanh::lean_ctor_get(v___x_2527_, 0);
                    v_isSharedCheck_2535_ = (!crate::leanh::lean_is_exclusive(v___x_2527_)) as u8;
                    if v_isSharedCheck_2535_ == 0 {
                        v___x_2530_ = v___x_2527_;
                        v_isShared_2531_ = v_isSharedCheck_2535_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2528_);
                        crate::leanh::lean_dec(v___x_2527_);
                        v___x_2530_ = crate::leanh::lean_box(0);
                        v_isShared_2531_ = v_isSharedCheck_2535_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_2531_ == 0 {
                    v___x_2533_ = v___x_2530_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2534_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
                    v___x_2533_ = v_reuseFailAlloc_2534_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2533_;
            }
            14 => {
                if crate::leanh::lean_obj_tag(v_ileanFileName_x3f_2413_) == 1 {
                    v_val_2541_ = crate::leanh::lean_ctor_get(v_ileanFileName_x3f_2413_, 0);
                    crate::leanh::lean_inc_ref(v___y_2538_);
                    v___x_2542_ = l_Lean_Language_SnapshotTree_getAll(v___y_2538_);
                    v___x_2543_ = lean_mk_empty_array_with_capacity(v___y_2539_);
                    v___x_2544_ = lean_array_get_size(v___x_2542_);
                    v___x_2545_ = lean_nat_dec_lt(v___y_2539_, v___x_2544_);
                    crate::leanh::lean_dec(v___y_2539_);
                    if v___x_2545_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2542_);
                        v___y_2511_ = v___y_2537_;
                        v___y_2512_ = v___y_2538_;
                        v___y_2513_ = v_val_2541_;
                        v___y_2514_ = v___y_2540_;
                        v___y_2515_ = v___x_2543_;
                        state = 11;
                        continue;
                    } else {
                        v___x_2546_ = lean_nat_dec_le(v___x_2544_, v___x_2544_);
                        if v___x_2546_ == 0 {
                            if v___x_2545_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2542_);
                                v___y_2511_ = v___y_2537_;
                                v___y_2512_ = v___y_2538_;
                                v___y_2513_ = v_val_2541_;
                                v___y_2514_ = v___y_2540_;
                                v___y_2515_ = v___x_2543_;
                                state = 11;
                                continue;
                            } else {
                                v___x_2547_ = 0usize;
                                v___x_2548_ = lean_usize_of_nat(v___x_2544_);
                                v___x_2549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(v___x_2542_, v___x_2547_, v___x_2548_, v___x_2543_);
                                crate::leanh::lean_dec_ref(v___x_2542_);
                                v___y_2511_ = v___y_2537_;
                                v___y_2512_ = v___y_2538_;
                                v___y_2513_ = v_val_2541_;
                                v___y_2514_ = v___y_2540_;
                                v___y_2515_ = v___x_2549_;
                                state = 11;
                                continue;
                            }
                        } else {
                            v___x_2550_ = 0usize;
                            v___x_2551_ = lean_usize_of_nat(v___x_2544_);
                            v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(v___x_2542_, v___x_2550_, v___x_2551_, v___x_2543_);
                            crate::leanh::lean_dec_ref(v___x_2542_);
                            v___y_2511_ = v___y_2537_;
                            v___y_2512_ = v___y_2538_;
                            v___y_2513_ = v_val_2541_;
                            v___y_2514_ = v___y_2540_;
                            v___y_2515_ = v___x_2552_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2539_);
                    crate::leanh::lean_dec(v_stx_2442_);
                    crate::leanh::lean_dec_ref(v___x_2430_);
                    v___y_2450_ = v___y_2537_;
                    v___y_2451_ = v___y_2538_;
                    v___y_2452_ = v___y_2540_;
                    state = 2;
                    continue;
                }
            }
            15 => {
                v___x_2564_ = crate::leanh::lean_box((v___x_2428_) as usize);
                v___x_2565_ = crate::leanh::lean_box((v___y_2555_) as usize);
                v___f_2566_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_runFrontend___lam__3___boxed as *mut core::ffi::c_void,
                    7,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_2566_, 0, v___y_2556_);
                crate::leanh::lean_closure_set(v___f_2566_, 1, v___y_2563_);
                crate::leanh::lean_closure_set(v___f_2566_, 2, v___y_2554_);
                crate::leanh::lean_closure_set(v___f_2566_, 3, v___y_2557_);
                crate::leanh::lean_closure_set(v___f_2566_, 4, v___x_2564_);
                crate::leanh::lean_closure_set(v___f_2566_, 5, v___x_2565_);
                v___x_2567_ = crate::leanh::lean_box(0);
                v___x_2568_ = l_Lean_profileitIOUnsafe___redArg(
                    v___y_2559_,
                    v___y_2558_,
                    v___f_2566_,
                    v___x_2567_,
                );
                if crate::leanh::lean_obj_tag(v___x_2568_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2568_, 1);
                    v___y_2537_ = v___y_2558_;
                    v___y_2538_ = v___y_2560_;
                    v___y_2539_ = v___y_2562_;
                    v___y_2540_ = v___y_2561_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2562_);
                    crate::leanh::lean_dec_ref(v___y_2561_);
                    crate::leanh::lean_dec_ref(v___y_2560_);
                    crate::leanh::lean_dec_ref(v___y_2558_);
                    crate::leanh::lean_dec(v_stx_2442_);
                    crate::leanh::lean_dec_ref(v___x_2434_);
                    crate::leanh::lean_dec_ref(v___x_2430_);
                    crate::leanh::lean_dec(v_mainModuleName_2410_);
                    v_a_2569_ = crate::leanh::lean_ctor_get(v___x_2568_, 0);
                    v_isSharedCheck_2576_ = (!crate::leanh::lean_is_exclusive(v___x_2568_)) as u8;
                    if v_isSharedCheck_2576_ == 0 {
                        v___x_2571_ = v___x_2568_;
                        v_isShared_2572_ = v_isSharedCheck_2576_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2569_);
                        crate::leanh::lean_dec(v___x_2568_);
                        v___x_2571_ = crate::leanh::lean_box(0);
                        v_isShared_2572_ = v_isSharedCheck_2576_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_2572_ == 0 {
                    v___x_2574_ = v___x_2571_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
                    v___x_2574_ = v_reuseFailAlloc_2575_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2574_;
            }
            18 => {
                if v___y_2582_ == 0 {
                    if crate::leanh::lean_obj_tag(v_oleanFileName_x3f_2412_) == 1 {
                        v_val_2585_ = crate::leanh::lean_ctor_get(v_oleanFileName_x3f_2412_, 0);
                        crate::leanh::lean_inc(v_val_2585_);
                        crate::leanh::lean_dec_ref_known(v_oleanFileName_x3f_2412_, 1);
                        v___x_2586_ = l_Lean_Elab_runFrontend___closed__3;
                        v___x_2587_ = l_Lean_MessageLog_empty;
                        crate::leanh::lean_inc_ref(v___y_2581_);
                        v___x_2588_ = l_Lean_Language_SnapshotTree_getAll(v___y_2581_);
                        v___x_2589_ = lean_array_get_size(v___x_2588_);
                        v___x_2590_ = lean_nat_dec_lt(v___y_2583_, v___x_2589_);
                        if v___x_2590_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2588_);
                            crate::leanh::lean_inc_ref(v___y_2578_);
                            v___y_2554_ = v___y_2578_;
                            v___y_2555_ = v___y_2579_;
                            v___y_2556_ = v___y_2580_;
                            v___y_2557_ = v_val_2585_;
                            v___y_2558_ = v___y_2578_;
                            v___y_2559_ = v___x_2586_;
                            v___y_2560_ = v___y_2581_;
                            v___y_2561_ = v___y_2584_;
                            v___y_2562_ = v___y_2583_;
                            v___y_2563_ = v___x_2587_;
                            state = 15;
                            continue;
                        } else {
                            v___x_2591_ = lean_nat_dec_le(v___x_2589_, v___x_2589_);
                            if v___x_2591_ == 0 {
                                if v___x_2590_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2588_);
                                    crate::leanh::lean_inc_ref(v___y_2578_);
                                    v___y_2554_ = v___y_2578_;
                                    v___y_2555_ = v___y_2579_;
                                    v___y_2556_ = v___y_2580_;
                                    v___y_2557_ = v_val_2585_;
                                    v___y_2558_ = v___y_2578_;
                                    v___y_2559_ = v___x_2586_;
                                    v___y_2560_ = v___y_2581_;
                                    v___y_2561_ = v___y_2584_;
                                    v___y_2562_ = v___y_2583_;
                                    v___y_2563_ = v___x_2587_;
                                    state = 15;
                                    continue;
                                } else {
                                    v___x_2592_ = 0usize;
                                    v___x_2593_ = lean_usize_of_nat(v___x_2589_);
                                    v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v___x_2588_, v___x_2592_, v___x_2593_, v___x_2587_);
                                    crate::leanh::lean_dec_ref(v___x_2588_);
                                    crate::leanh::lean_inc_ref(v___y_2578_);
                                    v___y_2554_ = v___y_2578_;
                                    v___y_2555_ = v___y_2579_;
                                    v___y_2556_ = v___y_2580_;
                                    v___y_2557_ = v_val_2585_;
                                    v___y_2558_ = v___y_2578_;
                                    v___y_2559_ = v___x_2586_;
                                    v___y_2560_ = v___y_2581_;
                                    v___y_2561_ = v___y_2584_;
                                    v___y_2562_ = v___y_2583_;
                                    v___y_2563_ = v___x_2594_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                v___x_2595_ = 0usize;
                                v___x_2596_ = lean_usize_of_nat(v___x_2589_);
                                v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v___x_2588_, v___x_2595_, v___x_2596_, v___x_2587_);
                                crate::leanh::lean_dec_ref(v___x_2588_);
                                crate::leanh::lean_inc_ref(v___y_2578_);
                                v___y_2554_ = v___y_2578_;
                                v___y_2555_ = v___y_2579_;
                                v___y_2556_ = v___y_2580_;
                                v___y_2557_ = v_val_2585_;
                                v___y_2558_ = v___y_2578_;
                                v___y_2559_ = v___x_2586_;
                                v___y_2560_ = v___y_2581_;
                                v___y_2561_ = v___y_2584_;
                                v___y_2562_ = v___y_2583_;
                                v___y_2563_ = v___x_2597_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_2580_);
                        crate::leanh::lean_dec(v_oleanFileName_x3f_2412_);
                        v___y_2537_ = v___y_2578_;
                        v___y_2538_ = v___y_2581_;
                        v___y_2539_ = v___y_2583_;
                        v___y_2540_ = v___y_2584_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2584_);
                    crate::leanh::lean_dec(v___y_2583_);
                    crate::leanh::lean_dec_ref(v___y_2581_);
                    crate::leanh::lean_dec_ref(v___y_2580_);
                    crate::leanh::lean_dec_ref(v___y_2578_);
                    crate::leanh::lean_dec(v_stx_2442_);
                    crate::leanh::lean_dec_ref(v___x_2434_);
                    crate::leanh::lean_dec_ref(v___x_2430_);
                    crate::leanh::lean_dec(v_oleanFileName_x3f_2412_);
                    crate::leanh::lean_dec(v_mainModuleName_2410_);
                    v___x_2598_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2598_, 0, v___x_2438_);
                    return v___x_2598_;
                }
            }
            19 => {
                crate::leanh::lean_inc_ref(v___y_2600_);
                v___x_2603_ = l_Lean_Language_SnapshotTree_runAndReport(
                    v___y_2600_,
                    v___x_2434_,
                    v_jsonOutput_2414_,
                    v___y_2602_,
                );
                crate::leanh::lean_dec(v___y_2602_);
                if crate::leanh::lean_obj_tag(v___x_2603_) == 0 {
                    v_a_2604_ = crate::leanh::lean_ctor_get(v___x_2603_, 0);
                    v_isSharedCheck_2631_ = (!crate::leanh::lean_is_exclusive(v___x_2603_)) as u8;
                    if v_isSharedCheck_2631_ == 0 {
                        v___x_2606_ = v___x_2603_;
                        v_isShared_2607_ = v_isSharedCheck_2631_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2604_);
                        crate::leanh::lean_dec(v___x_2603_);
                        v___x_2606_ = crate::leanh::lean_box(0);
                        v_isShared_2607_ = v_isSharedCheck_2631_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2601_);
                    crate::leanh::lean_dec_ref(v___y_2600_);
                    crate::leanh::lean_dec(v_stx_2442_);
                    crate::leanh::lean_dec_ref(v___x_2439_);
                    crate::leanh::lean_dec_ref(v___x_2434_);
                    crate::leanh::lean_dec_ref(v___x_2430_);
                    crate::leanh::lean_dec(v_oleanFileName_x3f_2412_);
                    crate::leanh::lean_dec(v_mainModuleName_2410_);
                    v_a_2632_ = crate::leanh::lean_ctor_get(v___x_2603_, 0);
                    v_isSharedCheck_2639_ = (!crate::leanh::lean_is_exclusive(v___x_2603_)) as u8;
                    if v_isSharedCheck_2639_ == 0 {
                        v___x_2634_ = v___x_2603_;
                        v_isShared_2635_ = v_isSharedCheck_2639_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2632_);
                        crate::leanh::lean_dec(v___x_2603_);
                        v___x_2634_ = crate::leanh::lean_box(0);
                        v_isShared_2635_ = v_isSharedCheck_2639_;
                        state = 24;
                        continue;
                    }
                }
            }
            20 => {
                v___x_2608_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___x_2439_);
                if crate::leanh::lean_obj_tag(v___x_2608_) == 1 {
                    crate::leanh::lean_del_object(v___x_2606_);
                    v_val_2609_ = crate::leanh::lean_ctor_get(v___x_2608_, 0);
                    crate::leanh::lean_inc(v_val_2609_);
                    crate::leanh::lean_dec_ref_known(v___x_2608_, 1);
                    v_env_2610_ = crate::leanh::lean_ctor_get(v_val_2609_, 0);
                    crate::leanh::lean_inc_ref(v_env_2610_);
                    v_scopes_2611_ = crate::leanh::lean_ctor_get(v_val_2609_, 2);
                    crate::leanh::lean_inc(v_scopes_2611_);
                    crate::leanh::lean_dec(v_val_2609_);
                    crate::leanh::lean_inc(v___y_2601_);
                    v___x_2612_ =
                        l_List_get_x21Internal___redArg(v___x_2445_, v_scopes_2611_, v___y_2601_);
                    crate::leanh::lean_dec(v_scopes_2611_);
                    if v_printStats_2417_ == 0 {
                        v_opts_2613_ = crate::leanh::lean_ctor_get(v___x_2612_, 1);
                        crate::leanh::lean_inc_ref(v_opts_2613_);
                        crate::leanh::lean_dec(v___x_2612_);
                        v___x_2614_ = (crate::leanh::lean_unbox(v_a_2604_) as u8);
                        v___x_2615_ = (crate::leanh::lean_unbox(v_a_2604_) as u8);
                        crate::leanh::lean_dec(v_a_2604_);
                        crate::leanh::lean_inc_ref(v_env_2610_);
                        v___y_2578_ = v_opts_2613_;
                        v___y_2579_ = v___x_2614_;
                        v___y_2580_ = v_env_2610_;
                        v___y_2581_ = v___y_2600_;
                        v___y_2582_ = v___x_2615_;
                        v___y_2583_ = v___y_2601_;
                        v___y_2584_ = v_env_2610_;
                        state = 18;
                        continue;
                    } else {
                        v_opts_2616_ = crate::leanh::lean_ctor_get(v___x_2612_, 1);
                        crate::leanh::lean_inc_ref(v_opts_2616_);
                        crate::leanh::lean_dec(v___x_2612_);
                        crate::leanh::lean_inc_ref(v_env_2610_);
                        v___x_2617_ = l_Lean_Environment_displayStats(v_env_2610_);
                        if crate::leanh::lean_obj_tag(v___x_2617_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2617_, 1);
                            v___x_2618_ = (crate::leanh::lean_unbox(v_a_2604_) as u8);
                            v___x_2619_ = (crate::leanh::lean_unbox(v_a_2604_) as u8);
                            crate::leanh::lean_dec(v_a_2604_);
                            crate::leanh::lean_inc_ref(v_env_2610_);
                            v___y_2578_ = v_opts_2616_;
                            v___y_2579_ = v___x_2618_;
                            v___y_2580_ = v_env_2610_;
                            v___y_2581_ = v___y_2600_;
                            v___y_2582_ = v___x_2619_;
                            v___y_2583_ = v___y_2601_;
                            v___y_2584_ = v_env_2610_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_opts_2616_);
                            crate::leanh::lean_dec_ref(v_env_2610_);
                            crate::leanh::lean_dec(v_a_2604_);
                            crate::leanh::lean_dec(v___y_2601_);
                            crate::leanh::lean_dec_ref(v___y_2600_);
                            crate::leanh::lean_dec(v_stx_2442_);
                            crate::leanh::lean_dec_ref(v___x_2434_);
                            crate::leanh::lean_dec_ref(v___x_2430_);
                            crate::leanh::lean_dec(v_oleanFileName_x3f_2412_);
                            crate::leanh::lean_dec(v_mainModuleName_2410_);
                            v_a_2620_ = crate::leanh::lean_ctor_get(v___x_2617_, 0);
                            v_isSharedCheck_2627_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2617_)) as u8;
                            if v_isSharedCheck_2627_ == 0 {
                                v___x_2622_ = v___x_2617_;
                                v_isShared_2623_ = v_isSharedCheck_2627_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2620_);
                                crate::leanh::lean_dec(v___x_2617_);
                                v___x_2622_ = crate::leanh::lean_box(0);
                                v_isShared_2623_ = v_isSharedCheck_2627_;
                                state = 21;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2608_);
                    crate::leanh::lean_dec(v_a_2604_);
                    crate::leanh::lean_dec(v___y_2601_);
                    crate::leanh::lean_dec_ref(v___y_2600_);
                    crate::leanh::lean_dec(v_stx_2442_);
                    crate::leanh::lean_dec_ref(v___x_2434_);
                    crate::leanh::lean_dec_ref(v___x_2430_);
                    crate::leanh::lean_dec(v_oleanFileName_x3f_2412_);
                    crate::leanh::lean_dec(v_mainModuleName_2410_);
                    if v_isShared_2607_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2606_, 0, v___x_2438_);
                        v___x_2629_ = v___x_2606_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_2630_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2438_);
                        v___x_2629_ = v_reuseFailAlloc_2630_;
                        state = 23;
                        continue;
                    }
                }
            }
            21 => {
                if v_isShared_2623_ == 0 {
                    v___x_2625_ = v___x_2622_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2626_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
                    v___x_2625_ = v_reuseFailAlloc_2626_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2625_;
            }
            23 => {
                return v___x_2629_;
            }
            24 => {
                if v_isShared_2635_ == 0 {
                    v___x_2637_ = v___x_2634_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
                    v___x_2637_ = v_reuseFailAlloc_2638_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2637_;
            }
            26 => {
                v_stx_x3f_2642_ = crate::leanh::lean_ctor_get(v_metaSnap_2441_, 0);
                crate::leanh::lean_inc(v_stx_x3f_2642_);
                v_reportingRange_2643_ = crate::leanh::lean_ctor_get(v_metaSnap_2441_, 1);
                crate::leanh::lean_inc(v_reportingRange_2643_);
                v___x_2644_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_metaSnap_2441_,
                    v___f_2444_,
                    v_stx_x3f_2642_,
                    v_reportingRange_2643_,
                    v___x_2428_,
                );
                v___x_2645_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2646_ = lean_mk_empty_array_with_capacity(v___x_2645_);
                v___x_2647_ = lean_array_push(v___x_2646_, v___x_2644_);
                v___x_2648_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2641_, v___x_2647_);
                v___x_2649_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2649_, 0, v_toSnapshot_2440_);
                crate::leanh::lean_ctor_set(v___x_2649_, 1, v___x_2648_);
                v___x_2650_ = crate::leanh::lean_box(1);
                v___x_2651_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2652_ = lean_array_get_size(v_errorOnKinds_2415_);
                v___x_2653_ = lean_nat_dec_lt(v___x_2651_, v___x_2652_);
                if v___x_2653_ == 0 {
                    v___y_2600_ = v___x_2649_;
                    v___y_2601_ = v___x_2651_;
                    v___y_2602_ = v___x_2650_;
                    state = 19;
                    continue;
                } else {
                    v___x_2654_ = lean_nat_dec_le(v___x_2652_, v___x_2652_);
                    if v___x_2654_ == 0 {
                        if v___x_2653_ == 0 {
                            v___y_2600_ = v___x_2649_;
                            v___y_2601_ = v___x_2651_;
                            v___y_2602_ = v___x_2650_;
                            state = 19;
                            continue;
                        } else {
                            v___x_2655_ = 0usize;
                            v___x_2656_ = lean_usize_of_nat(v___x_2652_);
                            v___x_2657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_errorOnKinds_2415_, v___x_2655_, v___x_2656_, v___x_2650_);
                            v___y_2600_ = v___x_2649_;
                            v___y_2601_ = v___x_2651_;
                            v___y_2602_ = v___x_2657_;
                            state = 19;
                            continue;
                        }
                    } else {
                        v___x_2658_ = 0usize;
                        v___x_2659_ = lean_usize_of_nat(v___x_2652_);
                        v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_errorOnKinds_2415_, v___x_2658_, v___x_2659_, v___x_2650_);
                        v___y_2600_ = v___x_2649_;
                        v___y_2601_ = v___x_2651_;
                        v___y_2602_ = v___x_2660_;
                        state = 19;
                        continue;
                    }
                }
            }
            27 => {
                v_processedSnap_2665_ = crate::leanh::lean_ctor_get(v_val_2661_, 1);
                crate::leanh::lean_inc_ref(v_processedSnap_2665_);
                crate::leanh::lean_dec(v_val_2661_);
                v_stx_x3f_2666_ = crate::leanh::lean_ctor_get(v_processedSnap_2665_, 0);
                crate::leanh::lean_inc(v_stx_x3f_2666_);
                v_reportingRange_2667_ = crate::leanh::lean_ctor_get(v_processedSnap_2665_, 1);
                crate::leanh::lean_inc(v_reportingRange_2667_);
                v___f_2668_ = l_Lean_Elab_runFrontend___closed__4;
                v___x_2669_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_processedSnap_2665_,
                    v___f_2668_,
                    v_stx_x3f_2666_,
                    v_reportingRange_2667_,
                    v___x_2428_,
                );
                if v_isShared_2664_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2663_, 0, v___x_2669_);
                    v___x_2671_ = v___x_2663_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2672_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2669_);
                    v___x_2671_ = v_reuseFailAlloc_2672_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___y_2641_ = v___x_2671_;
                state = 26;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_runFrontend___boxed(
    mut v_input_2674_: *mut crate::leanh::LeanObject,
    mut v_opts_2675_: *mut crate::leanh::LeanObject,
    mut v_fileName_2676_: *mut crate::leanh::LeanObject,
    mut v_mainModuleName_2677_: *mut crate::leanh::LeanObject,
    mut v_trustLevel_2678_: *mut crate::leanh::LeanObject,
    mut v_oleanFileName_x3f_2679_: *mut crate::leanh::LeanObject,
    mut v_ileanFileName_x3f_2680_: *mut crate::leanh::LeanObject,
    mut v_jsonOutput_2681_: *mut crate::leanh::LeanObject,
    mut v_errorOnKinds_2682_: *mut crate::leanh::LeanObject,
    mut v_plugins_2683_: *mut crate::leanh::LeanObject,
    mut v_printStats_2684_: *mut crate::leanh::LeanObject,
    mut v_setup_x3f_2685_: *mut crate::leanh::LeanObject,
    mut v_a_2686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_trustLevel_boxed_2687_: u32 = 0;
    let mut v_jsonOutput_boxed_2688_: u8 = 0;
    let mut v_printStats_boxed_2689_: u8 = 0;
    let mut v_res_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_trustLevel_boxed_2687_ = crate::leanh::lean_unbox_uint32(v_trustLevel_2678_);
    crate::leanh::lean_dec(v_trustLevel_2678_);
    v_jsonOutput_boxed_2688_ = (crate::leanh::lean_unbox(v_jsonOutput_2681_) as u8);
    v_printStats_boxed_2689_ = (crate::leanh::lean_unbox(v_printStats_2684_) as u8);
    v_res_2690_ = l_Lean_Elab_runFrontend(
        v_input_2674_,
        v_opts_2675_,
        v_fileName_2676_,
        v_mainModuleName_2677_,
        v_trustLevel_boxed_2687_,
        v_oleanFileName_x3f_2679_,
        v_ileanFileName_x3f_2680_,
        v_jsonOutput_boxed_2688_,
        v_errorOnKinds_2682_,
        v_plugins_2683_,
        v_printStats_boxed_2689_,
        v_setup_x3f_2685_,
    );
    crate::leanh::lean_dec_ref(v_errorOnKinds_2682_);
    crate::leanh::lean_dec(v_ileanFileName_x3f_2680_);
    return v_res_2690_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Frontend(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Language_Lean(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_References(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Profiler(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_PersistentLintLog(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ProfilerServer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Frontend(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Frontend(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Language_Lean(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_References(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_Profiler(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_PersistentLintLog(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_ProfilerServer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Frontend(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Frontend(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Frontend(builtin);
}
